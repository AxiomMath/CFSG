module

public import Certificates.Data.CFSGNative.Th.Core

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

structure V2 where
  lo : UInt64
  hi : UInt64
deriving Inhabited, DecidableEq

namespace V2

@[inline, expose] def zero : V2 := ⟨0, 0⟩

@[inline, expose] def xor (a b : V2) : V2 := ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

@[inline, expose] def beq (a b : V2) : Bool := a.lo == b.lo && a.hi == b.hi

@[inline, expose] def wf (a : V2) : Bool := a.hi >>> 48 == 0

@[inline, expose] def word (a : V2) (k : Nat) : UInt64 := if k = 0 then a.lo else a.hi

@[inline, expose] def testBit (a : V2) (j : Nat) : Bool :=
  ((a.word (j / 64) >>> (UInt64.ofNat (j % 64))) &&& 1) == 1

@[inline, expose] def setBit (a : V2) (j : Nat) : V2 :=
  let m : UInt64 := (1 : UInt64) <<< (UInt64.ofNat (j % 64))
  if j / 64 = 0 then { a with lo := a.lo ||| m } else { a with hi := a.hi ||| m }

@[expose] def ofFn (f : Nat → Bool) : V2 :=
  (List.range 112).foldl (fun v j => if f j then v.setBit j else v) zero

@[inline, expose] def hash (a : V2) : UInt64 := mix (a.lo ^^^ mix a.hi)

end V2

@[expose] def frEntry (rows : Array V2) (k c : Nat) : V2 :=
  (List.range 8).foldl
    (fun acc i => if (c >>> i) % 2 = 1 then acc.xor (rows[8 * k + i]?.getD V2.zero) else acc)
    V2.zero

@[expose] def frTable (rows : Array V2) : Array V2 :=
  Array.ofFn (n := 14 * 256) fun i => frEntry rows (i.val / 256) (i.val % 256)

@[inline, expose] def frByte (t : Array V2) (base : Nat) (w : UInt64) (s : UInt64) (acc : V2) :
    V2 :=
  acc.xor t[base + ((w >>> s) &&& 0xFF).toNat]!

@[inline, expose] def frWord (t : Array V2) (base : Nat) (w : UInt64) (acc : V2) : V2 :=
  let acc := frByte t base w 0 acc
  let acc := frByte t (base + 256) w 8 acc
  let acc := frByte t (base + 512) w 16 acc
  let acc := frByte t (base + 768) w 24 acc
  let acc := frByte t (base + 1024) w 32 acc
  let acc := frByte t (base + 1280) w 40 acc
  let acc := frByte t (base + 1536) w 48 acc
  frByte t (base + 1792) w 56 acc

@[inline, expose] def frWord6 (t : Array V2) (base : Nat) (w : UInt64) (acc : V2) : V2 :=
  let acc := frByte t base w 0 acc
  let acc := frByte t (base + 256) w 8 acc
  let acc := frByte t (base + 512) w 16 acc
  let acc := frByte t (base + 768) w 24 acc
  let acc := frByte t (base + 1024) w 32 acc
  frByte t (base + 1280) w 40 acc

@[inline, expose] def frApply (t : Array V2) (v : V2) : V2 :=
  frWord6 t 2048 v.hi (frWord t 0 v.lo V2.zero)

@[expose] def rowOfEntries (e : Array Nat) (i : Nat) : V2 :=
  V2.ofFn fun j => (e[i * 112 + j]?.getD 0) % 2 == 1

@[expose] def rowsOf (s : String) : Array V2 :=
  let e := (decodeEntries s).toArray
  Array.ofFn (n := 112) fun i => rowOfEntries e i.val

@[expose] def mulRows (X Y : Array V2) : Array V2 :=
  let t := frTable Y
  X.map fun x => frApply t x

@[expose] def idRows (_ : Unit := ()) : Array V2 := Array.ofFn (n := 112) fun i => V2.ofFn fun j => j == i.val

@[expose] def eqRows (X Y : Array V2) : Bool :=
  X.size == Y.size && (List.range X.size).all fun i => (X[i]?.getD V2.zero).beq (Y[i]?.getD V2.zero)

@[expose] def powRows (M : Array V2) : Nat → Array V2
  | 0 => idRows
  | e + 1 => mulRows (powRows M e) M

@[expose] def transposeRows (r : Array V2) : Array V2 :=
  Array.ofFn (n := 112) fun j => V2.ofFn fun i => (r[i]?.getD V2.zero).testBit j.val

@[expose] def invRows (X : Array V2) : Array V2 := Id.run do
  let mut m := X
  let mut r := idRows
  for c in [0:112] do
    let mut p := 112
    for i in [c:112] do
      if p == 112 && (m[i]!).testBit c then p := i
    if p < 112 then
      let mc := m[p]!
      let rc := r[p]!
      m := (m.set! p m[c]!).set! c mc
      r := (r.set! p r[c]!).set! c rc
      for i in [0:112] do
        if i != c && (m[i]!).testBit c then
          m := m.set! i ((m[i]!).xor mc)
          r := r.set! i ((r[i]!).xor rc)
  return r

@[expose] def wordRows (mats invs : Array (Array V2)) (w : List Int) : Array V2 :=
  w.foldl (fun acc l =>
    mulRows acc (if 0 < l then mats[l.toNat - 1]?.getD idRows else invs[(-l).toNat - 1]?.getD idRows))
    idRows

@[expose] def invsOK (mats invs : Array (Array V2)) : Bool :=
  mats.size == invs.size &&
    (List.range mats.size).all fun k => eqRows (mulRows mats[k]! invs[k]!) idRows

end CFSG.Sporadic.J4.Native
