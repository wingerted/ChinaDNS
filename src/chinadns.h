#include <fcntl.h>
#include <netdb.h>
#include <resolv.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>
#include <arpa/inet.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>
#include <nameser.h>
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

typedef struct {
    uint16_t id;
    struct timeval ts;
    char *buf;
    size_t buflen;
    struct sockaddr *addr;
    socklen_t addrlen;
} delay_buf_t;

typedef struct {
    uint16_t id;
    struct sockaddr *addr;
    socklen_t addrlen;
} id_addr_t;

typedef struct {
    int entries;
    struct in_addr *ips;
} ip_list_t;

typedef struct {
    struct in_addr net;
    in_addr_t mask;
} net_mask_t;

typedef struct {
    int entries;
    net_mask_t *nets;
} net_list_t;


// avoid malloc and free
#define BUF_SIZE 2048
static char global_buf[BUF_SIZE];

static int verbose = 0;

static int bidirectional = 0;

#if defined(PACKAGE_STRING)
static const char *version = PACKAGE_STRING;
#else
static const char *version = "ChinaDNS";
#endif

static const char *default_dns_servers =
       // "114.114.114.114,8.8.8.8,8.8.4.4,208.67.222.222:443,208.67.222.222:5353";
        "8.8.8.8";
static char *dns_servers = NULL;
static int dns_servers_len;
static id_addr_t *dns_server_addrs;

static int parse_args(int argc, char **argv);

static int setnonblock(int sock);
static int resolve_dns_servers();

static const char *default_listen_addr = "0.0.0.0";
static const char *default_listen_port = "53";

static char *listen_addr = NULL;
static char *listen_port = NULL;

static const char *default_ip_list_file = "iplist.txt";
static char *ip_list_file = NULL;
static ip_list_t ip_list;
static int parse_ip_list();

static char *chnroute_file = NULL;
static net_list_t chnroute_list;
static int parse_chnroute();
static int test_ip_in_list(struct in_addr ip, const net_list_t *netlist);

static int dns_init_sockets();
static void dns_handle_local();
static void dns_handle_remote();

static const char *hostname_from_question(ns_msg msg, int len);
static int should_filter_query(ns_msg msg, struct in_addr dns_addr);

static void queue_add(id_addr_t id_addr);
static id_addr_t *queue_lookup(uint16_t id);

#define ID_ADDR_QUEUE_LEN 128
// use a queue instead of hash here since it's not long
static id_addr_t id_addr_queue[ID_ADDR_QUEUE_LEN];
static int id_addr_queue_pos = 0;

#define EMPTY_RESULT_DELAY 0.3f
#define DELAY_QUEUE_LEN 128
static delay_buf_t delay_queue[DELAY_QUEUE_LEN];
static void schedule_delay(uint16_t query_id, const char *buf, size_t buflen,
        struct sockaddr *addr, socklen_t addrlen);
static void check_and_send_delay();
static void free_delay(int pos);
// next position for first, not used
static int delay_queue_first = 0;
// current position for last, used
static int delay_queue_last = 0;
static float empty_result_delay = EMPTY_RESULT_DELAY;

static int local_sock;
static int remote_sock;

static const char *help_message =
        "usage: chinadns [-h] [-l IPLIST_FILE] [-b BIND_ADDR] [-p BIND_PORT]\n"
                "       [-c CHNROUTE_FILE] [-s DNS] [-v]\n"
                "Forward DNS requests.\n"
                "\n"
                "  -h, --help            show this help message and exit\n"
                "  -l IPLIST_FILE        path to ip blacklist file\n"
                "  -c CHNROUTE_FILE      path to china route file\n"
                "                        if not specified, CHNRoute will be turned off\n"
                "  -d                    enable bi-directional CHNRoute filter\n"
                "  -y                    delay time for suspects, default: 0.3\n"
                "  -b BIND_ADDR          address that listens, default: 127.0.0.1\n"
                "  -p BIND_PORT          port that listens, default: 53\n"
                "  -s DNS                DNS servers to use, default:\n"
                "                        114.114.114.114,208.67.222.222:443,8.8.8.8\n"
                "  -v                    verbose logging\n"
                "\n"
                "Online help: <https://github.com/clowwindy/ChinaDNS-C>\n";

#define __LOG(o, t, v, s...) do {                                   \
  time_t now;                                                       \
  time(&now);                                                       \
  char *time_str = ctime(&now);                                     \
  time_str[strlen(time_str) - 1] = '\0';                            \
  if (t == 0) {                                                     \
    if (stdout != o || verbose) {                                   \
      fprintf(o, "%s ", time_str);                                  \
      fprintf(o, s);                                                \
      fflush(o);                                                    \
    }                                                               \
  } else if (t == 1) {                                              \
    fprintf(o, "%s %s:%d ", time_str, __FILE__, __LINE__);          \
    perror(v);                                                      \
  }                                                                 \
} while (0)

#define LOG(s...) __LOG(stdout, 0, "_", s)
#define ERR(s) __LOG(stderr, 1, s, "_")
#define VERR(s...) __LOG(stderr, 0, "_", s)

#ifdef DEBUG
#define DLOG(s...) LOG(s)
void __gcov_flush(void);
static void gcov_handler(int signum)
{
  __gcov_flush();
  exit(1);
}
#else
#define DLOG(s...)
#endif