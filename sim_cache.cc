#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <math.h>
#include <cstring>
#include <bitset>
#include <iostream>
using namespace std;

typedef unsigned long ulong;

#define ASSERT(condition, address) { if (!condition) { std::cout << "Stack Details: " << address << std::endl; assert(condition); }};
//#define DEBUG
#define Main

enum Flags {
	INVALID = 0, VALID = 1, DIRTY = 2
};
enum ReplacementPolices {
	LRU = 0, FIFO = 1, LFU = 2
};
enum MissType {
	Unknown = 0, ReadMiss = 1, WriteMiss = 2, Hit = 3
};
enum INCULSION {
	NON_INCULSION = 0, INCULSION = 1, EXCULSION = 2
};

volatile int REPL_POLICY;
volatile int INCLUSION_FLAG;
volatile bool L2_Exits;

class CacheLine {
private:
	ulong assoc, seq, index, tag, state;
public:
	CacheLine(ulong assoc) {
		this->assoc = assoc;
		this->seq = 0;
		this->index = 0;
		this->state = (INVALID);
	}
	~CacheLine() {
	}
	bool isValid() const {
		return (state != INVALID);
	}
	bool isDirty() const {
		return (state == DIRTY);
	}
	void incrementSeq() {
		++seq;
	}
	ulong getIndex() const {
		return index;
	}
	void setIndex(ulong index) {
		this->index = index;
	}
	ulong getSeq() const {
		return seq;
	}
	void setSeq(ulong seq) {
		this->seq = seq;
	}
	ulong getState() const {
		return state;
	}
	void setState(ulong state) {
		this->state = state;
	}
	ulong getTag() const {
		return tag;
	}
	void setTag(ulong tag) {
		this->tag = tag;
	}
};

class Cache {
private:
	ulong size, assoc, blocksize, numsets, log2blocksize;
	ulong reads, writes, readmisses, writemisses;
	ulong victim_addr;
	int misstype;
	ulong writebacks;
	bool writeBack, evicted;
	CacheLine*** cacheline;
	Cache* lowerCache;

public:
	ulong current_seq;
	ulong* Set_Counter;
	Cache(ulong size, ulong assoc, ulong blocksize) {
		if (assoc < 1) {
			cout << "Error in cache configuration!" << endl;
			exit(1);
		}
		writeBack = false;
		this->current_seq = 0;
		this->size = size;
		this->assoc = assoc;
		this->blocksize = blocksize;
		this->numsets = size / (assoc * blocksize);
		this->log2blocksize = (ulong) log2(blocksize);
		reads = readmisses = writes = writemisses = 0;
		writebacks = 0;
		Set_Counter = new ulong[numsets];
		this->cacheline = new CacheLine**[numsets];
		for (int i = 0; i < (int) numsets; ++i) {
			Set_Counter[i] = 0;
			cacheline[i] = new CacheLine*[assoc];
			for (int j = 0; j < (int) assoc; ++j) {
				cacheline[i][j] = new CacheLine(assoc);
			}
		}
		this->lowerCache = NULL;
	}

	CacheLine* fillblock(ulong address) {
		int index = getIndex(address);
		CacheLine* victim = getVictim(address);
		setVictimAddr(victim->getTag());
		if (victim != NULL && victim->isDirty()) {
			WriteBacks();
		}
		if (victim->isValid()) {
			// the block is evicted; used in LFU case only
			assert(victim->getTag() != 0);
			Set_Counter[index] = victim->getSeq();
		}
		victim->setTag(getTag(address));
		victim->setState(VALID);
		incrementLFU(victim, address);
		incrementLRU(victim);
		return victim;
	}

	inline void InitLowerCache(Cache* cache) {
		this->lowerCache = cache;
	}

	inline void incrementLFU(CacheLine* victim, ulong addr) {
		if (REPL_POLICY == LFU)
			victim->setSeq(Set_Counter[getIndex(addr)]);
	}

	inline void Read_Miss() {
		readmisses++;
		misstype = ReadMiss;
	}
	inline void Write_Miss() {
		writemisses++;
		misstype = WriteMiss;
	}

	int getMissType() const {
		return misstype;
	}

	void incrementLRU(CacheLine* cacheline) {
		if (REPL_POLICY == LFU)
			cacheline->incrementSeq();
		else
			cacheline->setSeq(++current_seq);
	}

	inline void WriteBacks() {
		writeBack = true;
		writebacks++;
	}

	bool isWriteBack() const {
		return writeBack;
	}

	inline ulong getAddress(ulong tag) const {
		return (tag << (log2blocksize));
	}

	inline ulong getTag(ulong address) const {
		return (address >> (log2blocksize));
	}

	bool isEvicted() const {
		return evicted;
	}

	ulong getMemoryTraffic() {
		Cache * cache = (L2_Exits) ? this->lowerCache : this;
		ulong memtraffic = cache->readmisses + cache->writemisses
				+ cache->writebacks;
		return memtraffic;
	}

	CacheLine* getVictim(ulong addr) {
		CacheLine* victim = NULL;
		ulong index = getIndex(addr);
		// Check whether there is any invalid cacheline in the set;
		// if there is one then go with it
		for (int i = 0; i < (int) assoc; ++i) {
			if (!cacheline[index][i]->isValid())
				return cacheline[index][i];
		}
		ASSERT((victim == NULL), addr);
		// Now if there is no invalid cacheline then evict one using repl policy
		if (victim == NULL) {
			evicted = true;
			victim = cacheline[index][0];
			for (int i = 1; i < (int) assoc; ++i) {
				if (cacheline[index][i]->getSeq() < victim->getSeq()) {
					victim = cacheline[index][i];
				}
			}
		}
		return victim;
	}

	ulong calculateAddress(ulong tag) const {
		return (tag << log2blocksize);
	}

	ulong getVictimAddr() const {
		return victim_addr;
	}

	void setVictimAddr(ulong tag) {
		if (!evicted)
			return;
		victim_addr = calculateAddress(tag);
	}

	void Invalidate(ulong addr) {
		CacheLine* cl = findblock(addr);
		if (cl) {
			if ((INCLUSION_FLAG == INCULSION) && lowerCache) {
				if (cl->isDirty()) {
					WriteBacks();
					lowerCache->WriteBacks();
				}
			}
			cl->setState(INVALID);
		}
	}

	ulong getIndex(ulong address) const {
		ulong index, tagslack;
		tagslack = (ulong) (numsets - 1);
		index = getTag(address) & tagslack;
		assert(index < numsets);
		return index;
	}

	CacheLine* findblock(ulong address) {
		ulong tag = getTag(address);
		CacheLine** cacheline = this->cacheline[getIndex(address)];
		for (int i = 0; i < (int) assoc; ++i) {
			if ((tag == cacheline[i]->getTag()) && cacheline[i]->isValid())
				return cacheline[i];
		}
		return NULL;
	}

	void accessblock(ulong address, char operation, bool L2_EXCL) {
		misstype = Unknown;
		evicted = writeBack = false;
		victim_addr = 0;
		if (operation == 'r')
			reads++;
		else
			writes++;
		CacheLine* cacheline = findblock(address);
		if (cacheline == NULL) {
			if (operation == 'w')
				Write_Miss();
			else
				Read_Miss();
			if (L2_EXCL)
				cacheline = fillblock(address);
		} else {
			misstype = Hit;
			if (REPL_POLICY != FIFO)
				incrementLRU(cacheline);
		}
		if (operation == 'w')
			cacheline->setState(DIRTY);
	}

	float getMissRates() {
		if (reads || writes) {
			float missrate = (float) (readmisses + writemisses)
					/ (reads + writes);
			return missrate;
		}
		return 0;
	}

	void printStats() {
		printf("============    Simulation results   ============\n");
		printf("a. number of L1 reads: 				%lu\n", reads);
		printf("b. number of L1 read misses:			%lu\n", readmisses);
		printf("c. number of L1 writes: 			%lu\n", writes);
		printf("d. number of L1 write misses:			%lu\n", writemisses);
		printf("e. L1 miss rate: 				%.4f\n", getMissRates());
		printf("f. number of L1->L2 writebacks:			%lu\n", writebacks);
		if (L2_Exits) {
			printf("g. number of L2 reads:  			%lu\n", lowerCache->reads);
			printf("h. number of L2 read misses:			%lu\n",
					lowerCache->readmisses);
			printf("i. number of L2 writes:				%lu\n", lowerCache->writes);
			printf("j. number of L2 write misses:			%lu\n",
					lowerCache->writemisses);
			printf("k. L2 miss rate: 				%.4f\n", lowerCache->getMissRates());
			printf("l. number of L2->Mem writebacks:		%lu\n",
					lowerCache->writebacks);
		} else {
			printf("g. number of L2 reads:  			%d\n", 0);
			printf("h. number of L2 read misses:			%d\n", 0);
			printf("i. number of L2 writes:				%d\n", 0);
			printf("j. number of L2 write misses:			%d\n", 0);
			printf("k. L2 miss rate: 				%.4f\n", (float) 0);
			printf("l. number of L2->Mem writebacks: 		%d\n", 0);
		}
		printf("m. total memory traffic: 			%lu\n", getMemoryTraffic());

	}
};

#ifdef Main
int main(int argc, char *argv[]) {
	char* fname;
	ulong address;
	ulong L1_size, blocksize, L1_assoc, L2_size, L2_assoc;
	FILE* pFile;
	if (argv[1] == NULL) {
		printf("Wrong input type: ");
		printf(
				".\\sim_cache <BLOCKSIZE> <L1_SIZE> <L1_ASSOC> <L2_SIZE> <L2_ASSOC> <REPLACEMENT_POLICY> <INCLUSION> <TRACE_FILE> \n");
		exit(0);
	}
	blocksize = atoi(argv[1]);
	L1_size = atoi(argv[2]);
	L1_assoc = atoi(argv[3]);
	L2_size = atoi(argv[4]);
	L2_assoc = atoi(argv[5]);
	REPL_POLICY = atoi(argv[6]);
	INCLUSION_FLAG = atoi(argv[7]);
	fname = argv[8];
	pFile = fopen(fname, "r");
	if (pFile == 0) {
		printf("Trace file read problem\n");
		exit(1);
	}
	printf("============ Simulator configuration ============\n");
	printf("BLOCKSIZE:         		%lu\n", blocksize);
	printf("L1_SIZE:           		%lu\n", L1_size);
	printf("L1_ASSOC:          		%lu\n", L1_assoc);
	printf("L2_SIZE:           		%lu\n", L2_size);
	printf("L2_ASSOC:          		%lu\n", L2_assoc);
	printf("REPLACEMENT POLICY:		%d\n", REPL_POLICY);
	printf("INCLUSION POLICY:		%d\n", INCLUSION_FLAG);
	printf("TRACE FILE:			%s\n", fname);
	Cache* L1_Cache = new Cache(L1_size, L1_assoc, blocksize);
	Cache* L2_Cache;
	L2_Exits = (L2_size == 0) ? false : true;
	if (L2_Exits) {
		L2_Cache = new Cache(L2_size, L2_assoc, blocksize);
		L1_Cache->InitLowerCache(L2_Cache);
	}
	char line[60];
#ifdef DEBUG
	int address_accessed = 0;
#endif
	while (fgets(line, 60, pFile) != NULL) {
		int count = 1;
		char* token = strtok(line, " ");
		char* operation;
		while (token != NULL) {
			switch (count) {
			case 1:
				operation = token;
				break;
			case 2:
				address = strtol(token, NULL, 16);
				break;
			}
			count++;
			token = strtok(NULL, " ");
		}
		// Make room for a cacheline in L1;
		L1_Cache->accessblock(address, operation[0], true);
		if (!L2_Exits)
			continue;
		if (INCLUSION_FLAG == INCULSION) {
			// If there is a miss, then it will evict something.. Right??
			if (L1_Cache->isWriteBack()) {
				L2_Cache->accessblock(L1_Cache->getVictimAddr(), 'w', true);
				if (L2_Cache->isEvicted())
					L1_Cache->Invalidate(L2_Cache->getVictimAddr());
			}
		}
		if (INCLUSION_FLAG == EXCULSION) {
			if (L1_Cache->getMissType() == Hit)
				L2_Cache->Invalidate(address);
			if (L1_Cache->isEvicted()) {
				L2_Cache->accessblock(L1_Cache->getVictimAddr(), 'w', true);
				if (!L1_Cache->isWriteBack())
					L2_Cache->findblock(L1_Cache->getVictimAddr())->setState(
							VALID);
			}
		}
		if (INCLUSION_FLAG == NON_INCULSION) {
			if (L1_Cache->isWriteBack())
				L2_Cache->accessblock(L1_Cache->getVictimAddr(), 'w', true);
		}
		// If there is a miss then access L2 cache to check whether it is there or not.
		if ((L1_Cache->getMissType() == ReadMiss)
				|| (L1_Cache->getMissType() == WriteMiss)) {
			// Find in L2 cache whether the block is there or not.
			bool flag = (INCLUSION_FLAG == EXCULSION) ? false : true;
			L2_Cache->accessblock(address, 'r', flag);
			// Based on the inclusion property we decide on the what to do
			// Starting here ->
			if (INCLUSION_FLAG == INCULSION) {
				if (L2_Cache->isEvicted())
					L1_Cache->Invalidate(L2_Cache->getVictimAddr());
			}
			if (INCLUSION_FLAG == EXCULSION) {
				if (L2_Cache->getMissType() == Hit) {
					if (L2_Cache->findblock(address)->isDirty())
						L1_Cache->findblock(address)->setState(DIRTY);
					L2_Cache->Invalidate(address);
				}
			}
		}

#ifdef DEBUG
		cout << "# " << dec << ++address_accessed << " : " << operation << " "
		<< hex << address << endl;
		L1_Cache->printStats();
		printf("-----------------------------------------------------------\n");
#endif
	}
	L1_Cache->printStats();
}
#endif
