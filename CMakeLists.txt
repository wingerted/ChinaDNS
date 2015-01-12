cmake_minimum_required(VERSION 2.8.4)
project(ChinaDNS_C)

INCLUDE_DIRECTORIES(/usr/local/include)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

set(SOURCE_FILES
    src/chinadns.c src/chinadns.h)

LINK_DIRECTORIES(/usr/local/lib)

add_executable(ChinaDNS_C ${SOURCE_FILES})

TARGET_LINK_LIBRARIES(ChinaDNS_C resolv)