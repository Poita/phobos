// Written in the D programming language.

/**
This module defines combinatorics stuff.

Source: $(PHOBOSSRC std/_combinatorics.d)

Macros:

WIKI = Phobos/StdCombinatorics

Copyright: Copyright by authors 2012-.

License: $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: $(WEB poita.org, Peter Alexander).
 */
module std.combinatorics;

import core.bitop;
import std.algorithm;
import std.array;
import std.conv;
import std.functional;
import std.range;
import std.traits;

version (unittest)
{
	import std.bigint;
	import std.conv;
	import std.stdio;
	import std.typetuple;
}

/**
   Computes the factorial of a non-negative integer.

   The factorial of $(D n) is defined to be the product of all integers
   between 1 and $(D n) (inclusive). The factorial of 0 is 1.
 */
Int factorial(Int = ulong)(uint n)
{
	// TODO: use lookup tables
	// TODO: handle floats
	if (n < 2)
		return 1;
	Int result = cast(Int) n;
	while (--n != 1)
		result *= n; // TODO: handle overflow
	return result;
}

unittest
{
	foreach (T; TypeTuple!(short, ushort, int, uint, long, ulong))
	{
		assert(equal(iota(8).map!(factorial!T)(), [1, 1, 2, 6, 24, 120, 720, 5040]));
	}

	assert(factorial!ulong(20) == 2_432_902_008_176_640_000UL);
	// TODO: test bigint
}

/**
   Computes the multinomial coefficient of a set of integers.
 */
Int multinomial(Int, Range)(Range ks)
{
	// TODO: use better algo to avoid intermediate overflow
	// http://home.comcast.net/~tamivox/dave/multinomial/index.html
 	alias reduce!((a, b) => a + b) sum;
 	alias reduce!((a, b) => cast(Int)(a * b)) product;
 	alias factorial!Int fact;

 	uint n = sum(0u, ks);
 	return to!Int(fact(n) / product(cast(Int) 1, map!fact(ks)));
}

/**
   Computes the binomial coefficient.
 */
Int binomial(Int)(uint n, uint k)
{
	if (k > n)
		return 0;
	k = min(k, n - k);
	Int c = 1;
	foreach (uint i; 1..k+1)
	{
		// TODO: possible intermediate overflow
		c *= (n - (k - i));
		c /= i;
	}
	return c;
}

unittest
{
	int[][] pascal = [
		[1],
		[1,  1],
		[1,  2,  1],
		[1,  3,  3,  1],
		[1,  4,  6,  4,  1],
		[1,  5,  10, 10, 5,  1],
		[1,  6,  15, 20, 15, 6,  1]
	];
	foreach (T; TypeTuple!(short, ushort, int, uint, long, ulong))
	{
		alias binomial!T bc;
		foreach (n; 0..pascal.length)
			foreach (k; 0..pascal[n].length)
				assert(bc(n, k) == pascal[n][k]);
		assert(bc(26, 3) == 2600);
		//assert(bc(31, 4) == 31465);
		// TODO: this overflows, need overflow-free algo
	}
}

/**
Next permutation.
 */
bool nextPermutation(alias pred = ((a, b) => a < b), Range)(Range r)
    if (isBidirectionalRange!Range &&
    	hasSwappableElements!Range &&
        is(typeof(binaryFun!pred(r.front, r.front)) : bool))
{
	// TODO: optimize for array
	if (!r.empty)
	{
		auto iter1 = r.save;
		auto iter2 = r.save;
		iter1.popBack();
		for (size_t n = 1; !iter1.empty; ++n)
		{ 
			alias binaryFun!pred comp;
			if (comp(iter1.back, iter2.back))
			{
				auto iter3 = r.save;
				while (!comp(iter1.back, iter3.back))
					iter3.popBack();
				swap(iter1.back, iter3.back);
				static if (hasSlicing!Range && hasLength!Range)
					reverse(r[r.length - n .. r.length]);
				else
					reverse(retro(r).takeExactly(n));
				return true;
			}
			iter1.popBack();
			iter2.popBack();
		}
		reverse(r);
	}
	return false;
} // TODO: add tests

/**
Previous permutation.
 */
bool previousPermutation(alias pred = ((a, b) => a < b), Range)(Range r)
    if (isBidirectionalRange!Range &&
    	hasSwappableElements!Range &&
        is(typeof(binaryFun!pred(r.front, r.front)) : bool))
{
	alias binaryFun!pred comp;
	return nextPermutation!((a, b) => comp(b, a), Range)(r);
} // TODO: add tests

/**
	Count the number of permutations of a range under an ordering predicate.
	Multisets are handled correctly.
 */
Int countPermutations(Int = ulong, alias pred = ((a, b) => a < b), Range)(Range r)
{
 	alias binaryFun!pred order;
 	alias binaryFun!((a, b) => !(order(a, b) || order(b, a))) equivalent;
 	alias unaryFun!(a => a[1]) groupCount;

 	// TODO: check order
	auto set = array(r);
	sort!order(set);
 	return multinomial!Int(set.group!equivalent().map!groupCount());
}

unittest
{
	assert(countPermutations(cast(int[]) []) == 1);
	assert(countPermutations([1]) == 1);
	assert(countPermutations([1, 2]) == 2);
	assert(countPermutations([1, 2, 3]) == 6);
	assert(countPermutations([3, 1, 2]) == 6);
	assert(countPermutations([1, 1, 1]) == 1);
	assert(countPermutations([1, 2, 1]) == 3);
	assert(countPermutations([2, 1, 2, 1]) == 6);
	// TODO: larger test
	// TODO: test more range types
}

auto permutations(alias pred = ((a, b) => a < b), Range)(Range r)
	if (isInputRange!Range &&
        is(typeof(binaryFun!pred(r.front, r.front)) : bool))
{
	return Permutations!(pred, ElementType!Range)(r);
}

private struct Permutations(alias pred = ((a, b) => a < b), Value)
{
 	alias binaryFun!pred comp;

	this(Range)(Range source)
	{
		_front = array(source.save);
		_back = array(source.save);
		_length = countPermutations!(size_t, pred)(_front);
		previousPermutation(_back);
		_onLast = equal(_front, _back);
		_done = false;
	}

	@property auto front() { return _front; }
	@property auto back() { return _back; }
	@property bool empty() const { return _done; }
	@property size_t length() const { return _length; }

	void popFront()
	{
		assert(!_done);
		nextPermutation!pred(_front);
		_done = _onLast;
		_onLast = equal(_front, _back);
		--_length;
	}

	void popBack()
	{
		assert(!_done);
		previousPermutation!pred(_back);
		_done = _onLast;
		_onLast = equal(_front, _back);
		--_length;
	}

	@property auto save()
	{
		Permutations copy = void;
		copy._front = _front.dup;
		copy._back = _back.dup;
		copy._length = _length;
		copy._onLast = _onLast;
		copy._done = _done;
		return copy;
	}

	// TODO: random access
	// TODO: different orders

	private Value[] _front;
	private Value[] _back;
	private size_t _length;
	private bool _onLast = false;
	private bool _done = false;
}

unittest
{
	alias filter!"true" F;
	int[][] perms123 = [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]];
	
	assert(equal!equal(permutations([1, 2, 3]), perms123));
	assert(equal!equal(permutations([1, 2, 3]).retro(), perms123.retro()));
	assert(equal!equal(permutations(chain([1, 2], [3])), perms123));
	assert(equal!equal(permutations(chain([1, 2], [3])).retro(), perms123.retro()));
	assert(permutations(iota(1)).filter!"true"().walkLength() == 1);
	assert(permutations(iota(2)).filter!"true"().walkLength() == 2);
	assert(permutations(iota(3)).filter!"true"().walkLength() == 6);
	assert(permutations(iota(4)).filter!"true"().walkLength() == 24);
	assert(permutations(iota(5)).filter!"true"().walkLength() == 120);
	assert(permutations(iota(6)).filter!"true"().walkLength() == 720);

	int[][] perms112 = [[1, 1, 2], [1, 2, 1], [2, 1, 1]];
	assert(equal!equal(permutations([1, 1, 2]), perms112));
	assert(equal!equal(permutations([1, 1, 2]).retro(), perms112.retro()));

	int[][] perms111 = [[1, 1, 1]];
	assert(equal!equal(permutations([1, 1, 1]), perms111));
	assert(equal!equal(permutations([1, 1, 1]).retro(), perms111));

	int[] emptyArray = [];
	assert(equal!equal(permutations(emptyArray), [emptyArray]));

	// TODO: test more range types
	// TODO: try larger permutations
}

/**
   Iterates a subset of a range, defined by a bitmask.
  */
struct Subset(Range)
	if (isInputRange!Range)
{
	// TODO: add bidir support
	// TODO: add random access support ???
	this(Range source, ulong mask) // TODO: support larger subsets
	{
		_current = source;
		_mask = mask;
		_length = popcnt(cast(uint) mask) + popcnt(cast(uint)(mask >> 32));
		static if (hasLength!Range)
			assert(_length <= _current.length, "Mask invalid for range.");
		moveNext();
	}

	@property auto front() { return _current.front; }
	@property bool empty() const { return _length == 0; }
	@property size_t length() const { return _length; }

	void popFront()
	{
		_mask >>= 1;
		_current.popFront();
		--_length;
		moveNext();
	}

	static if (isForwardRange!Range)
		@property Subset save()
		{
			Subset copy = void;
			copy._current = _current.save;
			copy._mask = _mask;
			copy._length = _length;
			return copy;
			// TODO: tests
		}

	private void moveNext()
	{
		while ((_mask & 1) == 0 && _mask != 0 && !_current.empty)
		{
			// TODO: count trailing 0's and use popFrontN
			_mask >>= 1;
			_current.popFront();
		}
		assert(!(_current.empty && _mask != 0), "Mask invalid for range.");
	}

	private Range _current;
	private ulong _mask = 0;
	private size_t _length = 0;
}

/**
   Returns the subset of $(D range) defined by $(D mask). The $(D n)th element
   of $(D range) will be present in the subset if the ($ n)th bit is set in
   $(D mask).
  */
Subset!Range subset(Range)(Range range, ulong mask)
	if (isInputRange!Range)
{
	return Subset!Range(range, mask);
}

unittest 
{
	dstring a = "abc"d;
	assert(equal(subset(a, 0), ""));
	assert(equal(subset(a, 1), "a"));
	assert(equal(subset(a, 2), "b"));
	assert(equal(subset(a, 3), "ab"));
	assert(equal(subset(a, 4), "c"));
	assert(equal(subset(a, 5), "ac"));
	assert(equal(subset(a, 6), "bc"));
	assert(equal(subset(a, 7), "abc"));

	assert(equal(subset(iota(64), 0xFFFF_FFFF_FFFF_FFFF), iota(64)));
	assert(equal(subset(iota(64), 0x0000_0000_FFFF_FFFF), iota(32)));
	assert(equal(subset(iota(64), 0xFFFF_FFFF_0000_0000), iota(32, 64)));
	assert(equal(subset(iota(64), 0x0000_FFFF_FFFF_0000), iota(16, 48)));
	assert(equal(subset(iota(64), 0x5555_5555_5555_5555), iota(0, 64, 2)));
	assert(equal(subset(iota(64), 0xAAAA_AAAA_AAAA_AAAA), iota(1, 64, 2)));
	assert(equal(subset(iota(64), (1UL << 17) | (1UL << 63)), [17, 63]));

	// TODO: test more range types
}

struct PowerSet(Range)
	if (isForwardRange!Range)
{
	// TODO: different orderings (colex etc.)

	enum infinite = isInfinite!Range;

	this(Range source)
	{
		_source = source;
		static if (!infinite)
		{
			auto numElements = walkLength(_source.save);
			enum maxElements = 8 * size_t.sizeof - 1;
			assert(numElements <= maxElements, "Source range is too large for power set.");
			_length = (cast(size_t) 1) << numElements;
		}
	}

	@property Subset!Range front() { return subset(_source.save, _mask); }
	@property PowerSet!Range save() { return this; }
	Subset!Range opIndex(size_t i) { return subset(_source.save, _mask + i); }

	static if (infinite)
	{
		enum bool empty = false;
		void popFront() { ++_mask; }
	}
	else
	{
		@property bool empty() const { return _length == 0; }
		void popFront() { ++_mask; --_length; }
		@property auto back() { return subset(_source.save, _mask + _length - 1); }
		void popBack() { --_length; }
		@property size_t length() const { return _length; }

		PowerSet!Range opSlice(size_t from, size_t to)
		{
			assert(from >= 0, "Slice out of bounds.");
			assert(to - from <= _length, "Slice out of bounds.");

			PowerSet slice = void;
			slice._source = _source;
			slice._length = to - from;
			slice._mask = _mask + from;
			return slice;
		}
	}

	private Range _source;
	static if (!infinite)
		private size_t _length = 0;
	private size_t _mask = 0; // TODO: support > 63 elements
}

PowerSet!Range subsets(Range)(Range r)
	if (isForwardRange!Range)
{
	return PowerSet!Range(r);
}

unittest
{
	auto p123 = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]];
	auto p = subsets([1, 2, 3]);
	assert(equal!equal(p, p123));
	assert(equal!equal(retro(p), retro(p123)));
	assert(equal!equal(radial(p), radial(p123)));
	assert(equal!equal(filter!"true"(p), p123));
	assert(p.length == 8);
	assert(equal(p[0], p123[0]));
	assert(equal(p[5], p123[5]));
	assert(equal(p[7], p123[7]));
	assert(equal!equal(p[0..8], p123));
	assert(equal!equal(p[1..6], p123[1..6]));
	assert(equal!equal(p[1..5][2..4], p123[3..5]));
	assert(equal!equal(subsets(cycle([1, 2, 3])).take(8), p123));
	assert(equal!equal(subsets(iota(1, 4)), p123));

	auto p111 = [[], [1], [1], [1, 1], [1], [1, 1], [1, 1], [1, 1, 1]];
	assert(equal!equal(subsets([1, 1, 1]), p111));

	int[] emptySet = [];
	assert(equal!equal(subsets(emptySet), [emptySet]));
	assert(equal!equal(subsets([1]), [[], [1]]));
}

struct KSubsets(Range)
	if (isForwardRange!Range)
{
	// TODO: orderings
	// TODO: length
	// TODO: random access??
	// TODO: bidirectional?
	enum infinite = isInfinite!Range;

	this(Range range, size_t k)
	{
		_source = range.save;
		_mask = ((cast(size_t) 1) << k) - 1; // lowest k bits set
		static if (!infinite)
		{
			size_t n = walkLength(range);
			_length = binomial!size_t(n, k);
		}
	}

	@property auto front() { return subset(_source.save, _mask); }

	void popFront()
	{
		// See: http://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
		// TODO: this can be faster if processor has ctz support. See link.
		static if (!infinite)
		{
			if (--_length == 0)
				return;
		}
		else if (_mask == 0)
			return;

		size_t v = _mask;
		size_t t = (v | (v - 1)) + 1;  
		_mask = t | ((((t & -t) / (v & -v)) >> 1) - 1); 
	}

	static if (infinite)
	{
		enum bool empty = false;
	}
	else
	{
		@property bool empty() const { return _length == 0; }
		@property size_t length() const { return _length; }
	}

	Range _source;
	size_t _mask;
	static if (!infinite)
	{
		size_t _length;
	}
}

KSubsets!Range kSubsets(Range)(Range range, size_t k)
{
	return KSubsets!Range(range, k);
}

unittest
{
	int[] emptySet = [];
	int[][] ks0_0 = [[]];
	int[][] ks1_1 = [[1]];
	int[][] ks12_1 = [[1], [2]];
	int[][] ks12_2 = [[1, 2]];
	int[][] ks123_1 = [[1], [2], [3]];
	int[][] ks123_2 = [[1, 2], [1, 3], [2, 3]];
	int[][] ks123_3 = [[1, 2, 3]];
	int[][] ks1234_1 = [[1], [2], [3], [4]];
	int[][] ks1234_2 = [[1, 2], [1, 3], [2, 3], [1, 4], [2, 4], [3, 4]];
	int[][] ks1234_3 = [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]];
	int[][] ks1234_4 = [[1, 2, 3, 4]];

	assert(equal!equal(kSubsets(emptySet, 0), ks0_0));
	assert(equal!equal(kSubsets([1], 1), ks1_1));
	assert(equal!equal(kSubsets([1, 2], 1), ks12_1));
	assert(equal!equal(kSubsets([1, 2], 2), ks12_2));
	assert(equal!equal(kSubsets([1, 2, 3], 1), ks123_1));
	assert(equal!equal(kSubsets([1, 2, 3], 2), ks123_2));
	assert(equal!equal(kSubsets([1, 2, 3], 3), ks123_3));
	assert(equal!equal(kSubsets([1, 2, 3, 4], 1), ks1234_1));
	assert(equal!equal(kSubsets([1, 2, 3, 4], 2), ks1234_2));
	assert(equal!equal(kSubsets([1, 2, 3, 4], 3), ks1234_3));
	assert(equal!equal(kSubsets([1, 2, 3, 4], 4), ks1234_4));

	assert(equal!equal(kSubsets(cycle([1, 2, 3, 4]), 0).take(1), ks0_0));
	assert(equal!equal(kSubsets(cycle([1, 2, 3, 4]), 1).take(4), ks1234_1));
	assert(equal!equal(kSubsets(cycle([1, 2, 3, 4]), 2).take(6), ks1234_2));
	assert(equal!equal(kSubsets(cycle([1, 2, 3, 4]), 3).take(4), ks1234_3));
	assert(equal!equal(kSubsets(cycle([1, 2, 3, 4]), 4).take(1), ks1234_4));

	dstring alphabet = "abcdefghijklmnopqrstuvwxyz"d;
	assert(kSubsets(alphabet, 3).length == 2600);
	assert(equal!equal(kSubsets(alphabet, 3).drop(2597), ["vyz"d, "wyz"d, "xyz"d]));

	//TODO: more range types
}

Int countIntegerPartitions(Int)(size_t n)
{
	// TODO: what to do about large n?
	
	// Lookup table.
	static Int[] lut = [1];
	if (n < lut.length && lut[n] != 0)
		return lut[n];

	Int s = 0;
	long j = cast(long)(n - 1);
	uint k = 2;
	while (j >= 0)
	{
		Int t = countIntegerPartitions!Int(cast(size_t) j);
		if ((k / 2) % 2 == 0)
			s -= t;
		else
			s += t;
		j -= (k % 2 == 0) ? k / 2 : k;
		++k;
	}
	lut.length = max(lut.length, n + 1);
	lut[n] = s;
	return s;
}

unittest
{
	static immutable int[] first50 = [
		1, 		1, 		2, 		3, 		5, 		7, 		11, 	15,
		22, 	30, 	42, 	56, 	77, 	101, 	135, 	176,
		231, 	297, 	385, 	490, 	627, 	792, 	1002, 	1255,
		1575, 	1958, 	2436, 	3010, 	3718, 	4565, 	5604, 	6842,
		8349, 	10143, 	12310, 	14883, 	17977, 	21637, 	26015, 	31185,
		37338, 	44583, 	53174, 	63261, 	75175, 	89134, 	105558, 124754,
		147273, 173525
	]; 

	foreach (T; TypeTuple!(int, uint, long, ulong, size_t, BigInt))
		foreach (i; 0..50)
			assert(countIntegerPartitions!T(i) == first50[i]);

	assert(countIntegerPartitions!size_t(100) == 190_569_292);
	assert(countIntegerPartitions!BigInt(1000) == BigInt("24061467864032622473692149727991"));
}

struct IntegerPartitions(Int)
	if (isIntegral!Int)
{
	this(Int n)
	{
		_size = 1;
		_lastNon1 = 0;
		_buffer.length = n == 0 ? 1 : cast(size_t) n;
		_buffer[0] = n;
		_length = countIntegerPartitions!size_t(n);
	}

	@property const(Int)[] front() const { return _buffer[0.._size]; }
	@property bool empty() const { return _size == 0; }

	void popFront()
	{
		--_length;
		if (_buffer[0] == 1 || _buffer[0] == 0)
		{
			_size = 0;
			return;
		}

		assert(_size != 0);

		size_t i = _lastNon1;
		assert(_buffer[i] != 1);
		if (--_buffer[i] == 1)
			--_lastNon1;
		Int rem = cast(Int)(_size - i);
		++i;
		for (; rem != 0; rem -= _buffer[i++])
		{
			_buffer[i] = min(_buffer[i-1], rem);
			if (_buffer[i] != 1)
				_lastNon1 = i;
		}
		_size = i;
	}

	@property IntegerPartitions save() const
	{
		IntegerPartitions copy;
		copy._buffer = _buffer.dup;
		copy._size = _size;
		copy._lastNon1 = _lastNon1;
		return copy;
	}

	@property size_t length() const { return _length; }

	// TODO: bidir
	// TODO: random
	// TODO: orders

	private Int[] _buffer;
	private size_t _size;
	private size_t _lastNon1;
	private size_t _length;
}

IntegerPartitions!Int integerPartitions(Int)(Int n)
{
	return IntegerPartitions!Int(n);
}

unittest
{
	int[][] p5 = [[5], [4, 1], [3, 2], [3, 1, 1], [2, 2, 1], [2, 1, 1, 1], [1, 1, 1, 1, 1]];
	int[][] p4 = [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]];
	int[][] p3 = [[3], [2, 1], [1, 1, 1]];
	int[][] p2 = [[2], [1, 1]];
	int[][] p1 = [[1]];
	int[][] p0 = [[0]];
	assert(equal!equal(integerPartitions(5), p5));
	assert(equal!equal(integerPartitions(4), p4));
	assert(equal!equal(integerPartitions(3), p3));
	assert(equal!equal(integerPartitions(2), p2));
	assert(equal!equal(integerPartitions(1), p1));
	assert(equal!equal(integerPartitions(0), p0));
}


// TODO: belongs in std.order?
bool colexOrder(alias pred = ((a, b) => a < b), Range)(Range lhs, Range rhs)
	if (isForwardRange!Range &&
		is(typeof(binaryFun!pred(lhs.front, rhs.front)) : bool))
{
	alias binaryFun!pred comp;
 	alias binaryFun!((a, b) => !(comp(a, b) || comp(b, a))) equivalent;

 	// TODO: probably faster to start at back for bidir ranges
	for (; !lhs.empty; lhs.popFront(), rhs.popFront())
	{
		assert(!rhs.empty, "Cannot determine colex order of ranges of different length.");
		if (comp(lhs.front, rhs.front))
		{
			Range lhsRem = lhs.save;
			Range rhsRem = rhs.save;
			lhsRem.popFront();
			rhsRem.popFront();
			if (equal!equivalent(lhsRem, rhsRem))
				return true;
		}
	}
	assert(rhs.empty, "Cannot determine colex order of ranges of different length.");
	return false;
}

unittest
{
	//123 < 124 < 134 < 234 < 125 < 135 < 235 < 145 < 245 < 345 < 126 < 136 < 236 < 146 < 246 < 346 < 156 < 256 < 356 < 456

	alias unaryFun!(a => isSorted!colexOrder(a)) isInColexOrder;

	int[][] colex4 = [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]];
	assert(isSorted!colexOrder(colex4));
	assert(permutations(colex4).map!(isInColexOrder)().count(true) == 1);
}

// http://theory.cs.uvic.ca/dis/programs.html (lots of algos)
// http://www.keithschwarz.com/binary-subsets/ (lex subset)
// http://www.math.dartmouth.edu/archive/m68f07/public_html/lectec.pdf

// WANT:
// - ordering (lex, colex, grey, fastest)
// - integer k-partitions
// - set partitions
// - combinations
// - pascal numbers
// - bell numbers
// - catalan numbers
// - stirling numbers 1st + 2nd
// - fibonacci
// - integer compositions
// - algorithms for large/real values
// - words over alphabet
// - k-permutations
// - integer compositions (ordered partitions)
// - set compositions
// - derangements
// - even permutations
// - non-crossing partitions