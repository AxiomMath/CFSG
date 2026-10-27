module

public section

namespace CFSG.Sporadic.Th.Native

structure V4 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
deriving Inhabited, DecidableEq

namespace V4

@[inline, expose] def zero : V4 := ⟨0, 0, 0, 0⟩

@[inline, expose] def xor (a b : V4) : V4 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩

@[inline, expose] def beq (a b : V4) : Bool :=
  a.w0 == b.w0 && a.w1 == b.w1 && a.w2 == b.w2 && a.w3 == b.w3

@[inline, expose] def lt (a b : V4) : Bool :=
  if a.w3 != b.w3 then a.w3 < b.w3 else if a.w2 != b.w2 then a.w2 < b.w2
  else if a.w1 != b.w1 then a.w1 < b.w1 else a.w0 < b.w0

@[inline, expose] def isZero (a : V4) : Bool := a.w0 == 0 && a.w1 == 0 && a.w2 == 0 && a.w3 == 0

@[inline, expose] def wf (a : V4) : Bool := a.w3 >>> 56 == 0

@[inline, expose] def word (a : V4) (k : Nat) : UInt64 :=
  if k = 0 then a.w0 else if k = 1 then a.w1 else if k = 2 then a.w2 else a.w3

@[inline, expose] def testBit (a : V4) (j : Nat) : Bool :=
  ((a.word (j / 64) >>> (UInt64.ofNat (j % 64))) &&& 1) == 1

@[inline, expose] def setBit (a : V4) (j : Nat) : V4 :=
  let m : UInt64 := (1 : UInt64) <<< (UInt64.ofNat (j % 64))
  if j / 64 = 0 then { a with w0 := a.w0 ||| m }
  else if j / 64 = 1 then { a with w1 := a.w1 ||| m }
  else if j / 64 = 2 then { a with w2 := a.w2 ||| m }
  else { a with w3 := a.w3 ||| m }

@[expose] def dot (a b : V4) : Bool :=
  (List.range 248).foldl (fun acc j => acc ^^ (a.testBit j && b.testBit j)) false

@[expose] def ofFn (f : Nat → Bool) : V4 :=
  (List.range 248).foldl (fun v j => if f j then v.setBit j else v) zero

end V4

structure Key where
  u : V4
  v : V4
deriving Inhabited, DecidableEq

@[inline, expose] def canon (p q : V4) : Key :=
  let s := p.xor q
  let (a, b) := if q.lt p then (q, p) else (p, q)
  let b := if s.lt b then s else b
  let (a, b) := if b.lt a then (b, a) else (a, b)
  ⟨a, b⟩

@[inline, expose] def Key.isCanonical (k : Key) : Bool :=
  k.u.wf && k.v.wf && !k.u.isZero && k.u.lt k.v && k.v.lt (k.u.xor k.v)

@[inline, expose] def Key.beq (a b : Key) : Bool := a.u.beq b.u && a.v.beq b.v

@[inline, expose] def mix (x : UInt64) : UInt64 :=
  let x := x ^^^ (x >>> 30)
  let x := x * 0xbf58476d1ce4e5b9
  let x := x ^^^ (x >>> 27)
  let x := x * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

@[inline, expose] def Key.hash (k : Key) : UInt64 :=
  mix (k.u.w0 ^^^ mix (k.u.w1 ^^^ mix (k.u.w2 ^^^ mix (k.u.w3 ^^^ mix (k.v.w0 ^^^
    mix (k.v.w1 ^^^ mix (k.v.w2 ^^^ mix k.v.w3)))))))

@[expose] def frEntry (rows : Array V4) (k c : Nat) : V4 :=
  (List.range 8).foldl
    (fun acc i => if (c >>> i) % 2 = 1 then acc.xor (rows[8 * k + i]?.getD V4.zero) else acc)
    V4.zero

@[expose] def frTable (rows : Array V4) : Array V4 :=
  Array.ofFn (n := 31 * 256) fun i => frEntry rows (i.val / 256) (i.val % 256)

@[inline, expose] def frByte (t : Array V4) (base : Nat) (w : UInt64) (s : UInt64) (acc : V4) :
    V4 :=
  acc.xor t[base + ((w >>> s) &&& 0xFF).toNat]!

@[inline, expose] def frWord (t : Array V4) (base : Nat) (w : UInt64) (acc : V4) : V4 :=
  let acc := frByte t base w 0 acc
  let acc := frByte t (base + 256) w 8 acc
  let acc := frByte t (base + 512) w 16 acc
  let acc := frByte t (base + 768) w 24 acc
  let acc := frByte t (base + 1024) w 32 acc
  let acc := frByte t (base + 1280) w 40 acc
  let acc := frByte t (base + 1536) w 48 acc
  frByte t (base + 1792) w 56 acc

@[inline, expose] def frWord7 (t : Array V4) (base : Nat) (w : UInt64) (acc : V4) : V4 :=
  let acc := frByte t base w 0 acc
  let acc := frByte t (base + 256) w 8 acc
  let acc := frByte t (base + 512) w 16 acc
  let acc := frByte t (base + 768) w 24 acc
  let acc := frByte t (base + 1024) w 32 acc
  let acc := frByte t (base + 1280) w 40 acc
  frByte t (base + 1536) w 48 acc

@[inline, expose] def frApply (t : Array V4) (v : V4) : V4 :=
  let acc := frWord t 0 v.w0 V4.zero
  let acc := frWord t 2048 v.w1 acc
  let acc := frWord t 4096 v.w2 acc
  frWord7 t 6144 v.w3 acc

@[inline, expose] def imageKey (t : Array V4) (k : Key) : Key :=
  canon (frApply t k.u) (frApply t k.v)

@[inline, expose] def wsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

@[expose] def decodeEntries (s : String) : List Nat :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  (body.filter fun c => !wsChar c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

@[expose] def rowOfEntries (e : Array Nat) (i : Nat) : V4 :=
  V4.ofFn fun j => (e[i * 248 + j]?.getD 0) % 2 == 1

@[expose] def rowsOf (s : String) : Array V4 :=
  let e := (decodeEntries s).toArray
  Array.ofFn (n := 248) fun i => rowOfEntries e i.val

@[expose] def transposeRows (r : Array V4) : Array V4 :=
  Array.ofFn (n := 248) fun j => V4.ofFn fun i => (r[i]?.getD V4.zero).testBit j.val

@[expose] def mulRows (X Y : Array V4) : Array V4 :=
  let t := frTable Y
  X.map fun x => frApply t x

@[expose] def idRows (_ : Unit := ()) : Array V4 := Array.ofFn (n := 248) fun i => V4.ofFn fun j => j == i.val

@[expose] def eqRows (X Y : Array V4) : Bool :=
  X.size == Y.size && (List.range X.size).all fun i => (X[i]?.getD V4.zero).beq (Y[i]?.getD V4.zero)

@[inline, expose] def rd8 (b : ByteArray) (o : Nat) : UInt64 := (b.get! o).toUInt64

@[inline, expose] def readU64 (b : ByteArray) (o : Nat) : UInt64 :=
  rd8 b o ||| (rd8 b (o+1) <<< 8) ||| (rd8 b (o+2) <<< 16) ||| (rd8 b (o+3) <<< 24) |||
  (rd8 b (o+4) <<< 32) ||| (rd8 b (o+5) <<< 40) ||| (rd8 b (o+6) <<< 48) ||| (rd8 b (o+7) <<< 56)

@[inline, expose] def readU56 (b : ByteArray) (o : Nat) : UInt64 :=
  rd8 b o ||| (rd8 b (o+1) <<< 8) ||| (rd8 b (o+2) <<< 16) ||| (rd8 b (o+3) <<< 24) |||
  (rd8 b (o+4) <<< 32) ||| (rd8 b (o+5) <<< 40) ||| (rd8 b (o+6) <<< 48)

@[inline, expose] def readV4 (b : ByteArray) (o : Nat) : V4 :=
  ⟨readU64 b o, readU64 b (o+8), readU64 b (o+16), readU56 b (o+24)⟩

@[inline, expose] def readKey (b : ByteArray) (i : Nat) : Key :=
  ⟨readV4 b (62 * i), readV4 b (62 * i + 31)⟩

@[inline, expose] def pushBytes (b : ByteArray) (w : UInt64) (len : Nat) : ByteArray := Id.run do
  let mut b := b
  for j in [0:len] do
    b := b.push ((w >>> (UInt64.ofNat (8 * j))).toUInt8)
  return b

@[inline, expose] def pushV4 (b : ByteArray) (v : V4) : ByteArray :=
  pushBytes (pushBytes (pushBytes (pushBytes b v.w0 8) v.w1 8) v.w2 8) v.w3 7

@[inline, expose] def pushKey (b : ByteArray) (k : Key) : ByteArray := pushV4 (pushV4 b k.u) k.v

@[inline, expose] def readU32 (b : ByteArray) (i : Nat) : Nat :=
  let o := 4 * i
  (b.get! o).toNat ||| ((b.get! (o+1)).toNat <<< 8) ||| ((b.get! (o+2)).toNat <<< 16) |||
    ((b.get! (o+3)).toNat <<< 24)

@[inline, expose] def writeU32 (b : ByteArray) (i : Nat) (x : Nat) : ByteArray :=
  let o := 4 * i
  ((((b.set! o (UInt8.ofNat x)).set! (o+1) (UInt8.ofNat (x >>> 8))).set! (o+2)
    (UInt8.ofNat (x >>> 16))).set! (o+3) (UInt8.ofNat (x >>> 24)))

@[inline, expose] def pushU32 (b : ByteArray) (x : Nat) : ByteArray :=
  (((b.push (UInt8.ofNat x)).push (UInt8.ofNat (x >>> 8))).push (UInt8.ofNat (x >>> 16))).push
    (UInt8.ofNat (x >>> 24))

@[expose] def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    b := b.push 0
  return b

end CFSG.Sporadic.Th.Native
