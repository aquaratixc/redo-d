/* An implementation of the redo build system
   in portable C with zero dependencies

   http://cr.yp.to/redo.html
   https://jdebp.eu./FGA/introduction-to-redo.html
   https://github.com/apenwarr/redo/blob/master/README.md
   http://news.dieweltistgarnichtso.net/bin/redo-sh.html

   To the extent possible under law,
   Leah Neukirchen <leah@vuxu.org>
   has waived all copyright and related or neighboring rights to this work.

   http://creativecommons.org/publicdomain/zero/1.0/
   
   Translated to D (BetterC mode) by Bakharev Oleg (aquaratixc) <disconnectix@gmail.com>
*/


/*
##% ldc2 -betterC -release -Os -boundscheck=off redo.d
##% strip -s redo
*/

import core.stdc.inttypes; // for remove
import core.stdc.limits;
import core.stdc.stdio;
import core.stdc.stdarg;
import core.stdc.stdlib;
import core.stdc.string;



import core.sys.posix.fcntl;
import core.sys.posix.sys.stat;
import core.sys.posix.stdio : fopen;
import core.sys.posix.stdlib;
import core.sys.posix.unistd;


struct sha256 {
	ulong len;    /* processed message length */
	uint[8] h;   /* hash state */
	ubyte[64] buf; /* message block buffer */
};

static uint ror(uint n, int k) { return (n >> k) | (n << (32-k)); }
auto Ch(uint x, uint y, uint z)  { return (z ^ (x & (y ^ z))); }
auto Maj(uint x,uint y,uint z) { return ((x & y) | (z & (x | y))); }
auto S0(uint x)	   { return (ror(x,2) ^ ror(x,13) ^ ror(x,22)); }
auto S1(uint x)	   { return (ror(x,6) ^ ror(x,11) ^ ror(x,25)); }
auto R0(uint x)	   { return (ror(x,7) ^ ror(x,18) ^ (x>>3)); }
auto R1(uint x)	   { return (ror(x,17) ^ ror(x,19) ^ (x>>10)); }

enum uint[64] K = [
0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
];

static void processblock(ref sha256 s, ubyte* buf)
{
	uint[64] W;
	uint t1, t2, a, b, c, d, e, f, g, h;
	int i;

	for (i = 0; i < 16; i++) {
		W[i] = cast(uint) (buf[4*i] << 24);
		W[i] |= cast(uint) (buf[4*i+1]<<16);
		W[i] |= cast(uint) (buf[4*i+2]<<8);
		W[i] |= buf[4*i+3];
	}
	for (; i < 64; i++)
		W[i] = R1(W[i-2]) + W[i-7] + R0(W[i-15]) + W[i-16];
	a = s.h[0];
	b = s.h[1];
	c = s.h[2];
	d = s.h[3];
	e = s.h[4];
	f = s.h[5];
	g = s.h[6];
	h = s.h[7];
	for (i = 0; i < 64; i++) {
		t1 = h + S1(e) + Ch(e, f, g) + K[i] + W[i];
		t2 = S0(a) + Maj(a, b, c);
		h = g;
		g = f;
		f = e;
		e = d + t1;
		d = c;
		c = b;
		b = a;
		a = t1 + t2;
	}
	s.h[0] += a;
	s.h[1] += b;
	s.h[2] += c;
	s.h[3] += d;
	s.h[4] += e;
	s.h[5] += f;
	s.h[6] += g;
	s.h[7] += h;
}

static void pad(ref sha256 s)
{
	uint r = s.len % 64;
	auto ptr = s.buf.ptr;

	s.buf[r++] = 0x80;
	if (r > 56) {
		memset(ptr + r, 0, 64 - r);
		r = 0;
		processblock(s, s.buf.ptr);
	}
	memset(ptr + r, 0, 56 - r);
	s.len *= 8;
	s.buf[56] = cast(ubyte) (s.len >> 56);
	s.buf[57] = cast(ubyte) (s.len >> 48);
	s.buf[58] = cast(ubyte) (s.len >> 40);
	s.buf[59] = cast(ubyte) (s.len >> 32);
	s.buf[60] = cast(ubyte) (s.len >> 24);
	s.buf[61] = cast(ubyte) (s.len >> 16);
	s.buf[62] = cast(ubyte) (s.len >> 8);
	s.buf[63] = cast(ubyte) (s.len);
	processblock(s, s.buf.ptr);
}

static void sha256_init(ref sha256 s)
{
	s.len = 0;
	s.h[0] = 0x6a09e667;
	s.h[1] = 0xbb67ae85;
	s.h[2] = 0x3c6ef372;
	s.h[3] = 0xa54ff53a;
	s.h[4] = 0x510e527f;
	s.h[5] = 0x9b05688c;
	s.h[6] = 0x1f83d9ab;
	s.h[7] = 0x5be0cd19;
}

static void sha256_sum(ref sha256 s, ubyte* md)
{
	int i;

	pad(s);
	for (i = 0; i < 8; i++) {
		md[4*i] = cast(ubyte) (s.h[i] >> 24);
		md[4*i+1] = cast(ubyte) (s.h[i] >> 16);
		md[4*i+2] = cast(ubyte) (s.h[i] >> 8);
		md[4*i+3] = cast(ubyte) (s.h[i]);
	}
}

static void sha256_update(ref sha256 s, const void* m, ulong len)
{
	ubyte* p = cast(ubyte*) m;
	uint r = s.len % 64;
	auto ptr = s.buf.ptr;

	s.len += len;
	if (r) {
		if (len < 64 - r) {
			memcpy(ptr + r, p, len);
			return;
		}
		memcpy(ptr + r, p, 64 - r);
		len -= 64 - r;
		p += 64 - r;
		processblock(s, s.buf.ptr);
	}
	for (; len >= 64; len -= 64, p += 64)
		processblock(s, p);
	memcpy(ptr, p, len);
}

int dir_fd = -1;
int dep_fd = -1;
int poolwr_fd = -1;
int poolrd_fd = -1;
int level = -1;
int implicit_jobs = 1;
int kflag, jflag, xflag, fflag, sflag;

static void redo_ifcreate(int fd, char *target)
{
	//dprintf(fd, "-%s\n", target);
}

extern(C) static char* check_dofile(const char *fmt, ...)
{
	static char[PATH_MAX] dofile;

	va_list ap;
	va_start(ap, fmt);
	vsnprintf(dofile.ptr, dofile.sizeof, fmt, ap);
	va_end(ap);

	if (access(dofile.ptr, F_OK) == 0) {
		return dofile.ptr;
	} else {
		redo_ifcreate(dep_fd, dofile.ptr);
		return cast(char*) 0;
	}
}

/*
dir/base.a.b
	will look for dir/base.a.b.do,
	dir/default.a.b.do, dir/default.b.do, dir/default.do,
	default.a.b.do, default.b.do, and default.do.

this function assumes no / in target
*/
static char* find_dofile(char *target)
{
	char[PATH_MAX] updir;
	char *u = updir.ptr;
	char* dofile, s;
	stat_t st, ost;

	dofile = check_dofile("./%s.do", target);
	if (dofile)
		return dofile;

	*u++ = '.';
	*u++ = '/';
	*u = 0;

	st.st_dev = 0;
	ost.st_dev = 0;
	st.st_ino = 0;
	ost.st_ino = 0;

	while (1) {
		ost = st;

		if (stat(updir.ptr, &st) < 0)
			return cast(char*) 0;
		if (ost.st_dev == st.st_dev && ost.st_ino == st.st_ino)
			break;  // reached root dir, .. = .

		s = target;
		while (*s) {
			if (*s++ == '.') {
				dofile = check_dofile("%sdefault.%s.do", updir.ptr, s);
				if (dofile)
					return dofile;
			}
		}

		dofile = check_dofile("%sdefault.do", updir.ptr);
		if (dofile)
			return dofile;

		*u++ = '.';
		*u++ = '.';
		*u++ = '/';
		*u = 0;
	}

	return cast(char*) 0;
}

static int envfd(const char* name)
{
	long fd;
	
	char* s = getenv(name);
	if (!s)
		return -1;

	fd = strtol(s, null, 10);
	if (fd < 0 || fd > 255)
		fd = -1;

	return cast(int) fd;
}

static void setenvfd(const char* name, int i)
{
	char[16] buf;
	snprintf(buf.ptr, buf.sizeof, "%d", i);
	setenv(name, buf.ptr, 1);
}

static char* hashfile(int fd)
{
	static char[16] hex = "0123456789abcdef";
	static char[65] asciihash;

	sha256 ctx;
	ulong off = 0;
	char[4096] buf;
	char* a;
	char[32] hash;
	int i;
	ssize_t r;

	sha256_init(ctx);

	while ((r = pread(fd, cast(void*) buf, buf.sizeof, off)) > 0) {
		sha256_update(ctx, cast(void*) buf, r);
		off += r;
	}

	sha256_sum(ctx,  cast(ubyte*) hash);

	for (i = 0, a = asciihash.ptr; i < 32; i++) {
		*a++ = hex[hash[i] / 16];
		*a++ = hex[hash[i] % 16];
	}
	*a = 0;

	return asciihash.ptr;
}

static char* datefile(int fd)
{
	static char[17] hexdate;
	stat_t st;

	fstat(fd, &st);
	snprintf(hexdate.ptr, hexdate.sizeof, "%016llx", cast(ulong) st.st_ctime);

	return hexdate.ptr;
}

static int keepdir()
{
	//int fd = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
	int fd = open(".", O_RDONLY);
	if (fd < 0) {
		perror("dir open");
		printf("test");
		exit(-1);
	}
	return fd;
}

static char* targetchdir(char *target)
{
	char *base = strrchr(target, '/');
	if (base) {
		int fd;
		*base = 0;
		// wtf this ???
		//fd = openat(dir_fd, target, O_RDONLY | O_DIRECTORY);
		//fd = openat(dir_fd, target, O_RDONLY | 0x010000); // ditto 
		if (fd < 0) {
			perror("openat dir");
			exit(111);
		}
		*base = '/';
		if (fchdir(fd) < 0) {
			perror("chdir");
			exit(111);
		}
		close(fd);
		return base+1;
	} else {
		fchdir(dir_fd);
		return target;
	}
}

static char* targetdep(char *target)
{
	static char[PATH_MAX] buf;
	snprintf(buf.ptr, buf.sizeof, ".dep.%s", target);
	return buf.ptr;
}

static char* targetlock(char *target)
{
	static char[PATH_MAX] buf;
	snprintf(buf.ptr, buf.sizeof, ".lock.%s", target);
	return buf.ptr;
}

static int sourcefile(char* target)
{
	if (access(targetdep(target), F_OK) == 0)
		return 0;

	if (fflag < 0)
		return access(target, F_OK) == 0;

	return find_dofile(target) == cast(char*) 0;
}

static int check_deps(char* target)
{
	char *depfile;
	FILE *f;
	int ok = 1;
	int fd;
	int old_dir_fd = dir_fd;

	target = targetchdir(target);

	if (sourcefile(target))
		return 1;

	if (fflag > 0)
		return 0;

	depfile = targetdep(target);
	f = fopen(depfile, "r");
	if (!f)
		return 0;

	dir_fd = keepdir();

	while (ok && !feof(f)) {
		char[4096] line;
		char *hash = line.ptr + 1;
		char *timestamp = line.ptr + 1 + 64 + 1;
		char *filename = line.ptr + 1 + 64 + 1 + 16 + 1;

		if (fgets(line.ptr, line.sizeof, f)) {
			line[strlen(line.ptr)-1] = 0; 
			switch (line[0]) {
			case '-':  
				if (access(line.ptr+1, F_OK) == 0)
					ok = 0;
				break;
			case '=':  
				// wtf this ???
				//fd = open(filename, O_RDONLY);
				if (fd < 0) {
					ok = 0;
				} else {
					if (strncmp(timestamp, datefile(fd), 16) != 0 &&
					    strncmp(hash, hashfile(fd), 64) != 0)
						ok = 0;
					close(fd);
				}
				if (ok && strcmp(target, filename) != 0) {
					ok = check_deps(filename);
					fchdir(dir_fd);
				}
				break;
			case '!':  
			default:  
				ok = 0;
			}
		} else {
			if (!feof(f)) {
				ok = 0;
				break;
			}
		}
	}

	fclose(f);

	close(dir_fd);
	dir_fd = old_dir_fd;

	return ok;
}

char[PATH_MAX] uprel;

void compute_uprel()
{
	char* u = uprel.ptr;
	char* dp = getenv("REDO_DIRPREFIX");

	*u = 0;
	while (dp && *dp) {
		*u++ = '.';
		*u++ = '.';
		*u++ = '/';
		*u = 0;
		dp = strchr(dp + 1, '/');
	}
}

static int write_dep(int dep_fd, char *file)
{
	int fd = open(file, O_RDONLY);
	if (fd < 0)
		return 0;
	// wtf this ???
	// vdprintf(dep_fd, "=%s %s %s%s\n", hashfile(fd), datefile(fd), (*file == '/' ? "" : uprel), file);
	close(fd);
	return 0;
}

//extern(C) int fdprintf(int fd, char *fmt, ...) {
    //va_list ap;
    //FILE *f = fdopen(fd);
    //int rc;

    //va_start(ap, &fmt);
    //rc = vfprintf(f, fmt, ap);
    //fclose(f);
    //va_end(ap);
    //return rc;
//}

// dofile doesn't contain /
// target can contain /
static char* redo_basename(char *dofile, char *target)
{
	static char[PATH_MAX] buf;
	int stripext = 0;
	char *s;

	if (strncmp(dofile, "default.", 8) == 0)
		for (stripext = -1, s = dofile; *s; s++)
			if (*s == '.')
				stripext++;

	strncpy(buf.ptr, target, buf.sizeof);
	while (stripext-- > 0) {
		if (strchr(buf.ptr, '.')) {
			char *e = strchr(buf.ptr, '\0');
			while (*--e != '.')
				*e = 0;
			*e = 0;
		}
	}

	return buf.ptr;
}

static void record_deps(int targetc, char** targetv)
{
	int targeti = 0;
	int fd;

	dep_fd = envfd("REDO_DEP_FD");
	if (dep_fd < 0)
		return;

	fchdir(dir_fd);

	for (targeti = 0; targeti < targetc; targeti++) {
		fd = open(targetv[targeti], O_RDONLY);
		if (fd < 0)
			continue;
		write_dep(dep_fd, targetv[targeti]);
		close(fd);
	}
}


//extern(C) void main(int argc, char*[] argv)
//{
	//// имя файла для опытов
	//char* filename = cast(char*) "tcp_server.d";
	//// хэш сюда
	//char* hash, date;
	//// открываем файл и сохраняем на него дескриптор
    //int fd = open(filename, O_RDONLY);
    //// получаем хэш
    //hash = hashfile(fd);
    //date = datefile(fd);
    //// распечатать хэш
    //printf("%s\n", hash);
    //printf("%s\n", date);
    //// закрыть файл
    //close(fd);
//}

extern(C) int main(int argc, char** argv)
{
	char *program;
	int opt, i;

	dep_fd = envfd("REDO_DEP_FD");

	level = envfd("REDO_LEVEL");
	if (level < 0)
		level = 0;

	if ((program == strrchr(argv[0], '/')))
		program++;
	else
		program = argv[0];

	while ((opt = getopt(argc, argv, "+kxfsj:C:")) != -1) {
		switch (opt) {
		case 'k':
			setenvfd("REDO_KEEP_GOING", 1);
			break;
		case 'x':
			setenvfd("REDO_TRACE", 1);
			break;
		case 'f':
			setenvfd("REDO_FORCE", 1);
			break;
		case 's':
			setenvfd("REDO_STDOUT", 1);
			break;
		case 'j':
			setenv("JOBS", optarg, 1);
			break;
		case 'C':
			if (chdir(optarg) < 0) {
				perror("chdir");
				exit(-1);
			}
			break;
		default:
			fprintf(stderr, "usage: %s [-kfsx] [-jN] [-Cdir] [TARGETS...]\n", program);
			exit(1);
		}
	}
	argc -= optind;
	argv += optind;

	fflag = envfd("REDO_FORCE");
	kflag = envfd("REDO_KEEP_GOING");
	xflag = envfd("REDO_TRACE");
	sflag = envfd("REDO_STDOUT");

	dir_fd = keepdir();

	if (strcmp(program, "redo") == 0) {
		char[] all = cast(char[]) "all";
		char** argv_def =  cast(char**) [ all ];

		if (argc == 0) {
			argc = 1;
			argv = argv_def;
		}

		fflag = 1;
		//redo_ifchange(argc, argv);
		//procure();
	} else if (strcmp(program, "redo-ifchange") == 0) {
		compute_uprel();
		//redo_ifchange(argc, argv);
		record_deps(argc, argv);
		//procure();
	} else if (strcmp(program, "redo-ifcreate") == 0) {
		for (i = 0; i < argc; i++)
			redo_ifcreate(dep_fd, argv[i]);
	} else if (strcmp(program, "redo-always") == 0) {
		//dprintf(dep_fd, "!\n");
	} else if (strcmp(program, "redo-hash") == 0) {
		for (i = 0; i < argc; i++)
			write_dep(1, argv[i]);
	} else {
		fprintf(stderr, "not implemented %s\n", program);
		exit(-1);
	}

	return 0;
}
