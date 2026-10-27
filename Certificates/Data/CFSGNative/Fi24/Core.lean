module

public import Certificates.Data.CFSGNative.Fi24.Wide
public import Certificates.Data.CFSGNative.F3.Basic

public section

namespace CFSG.Sporadic.Fi24.Native

@[expose] def ofTrits (d : Nat) (f : Nat → Nat) : W :=
  Nat.fold d (fun j _ v => v.setTrit j (f j % 3)) W.zero

@[expose] def rowsOfSeed (d : Nat) (s : String) : Array W :=
  let e := (CFSG.F3.Native.decodeEntries s).toArray
  Array.ofFn (n := d) fun i => ofTrits d fun j => e[i.val * d + j]?.getD 0

@[expose] def transposeW (n d : Nat) (X : Array W) : Array W :=
  Array.ofFn (n := d) fun j => ofTrits n fun i => (X[i]?.getD W.zero).trit j.val

@[expose] def idW (d : Nat) : Array W := Array.ofFn (n := d) fun i => W.zero.setTrit i.val 1

@[expose] def frEntry (Y : Array W) (b x : Nat) : W :=
  Nat.fold 8 (fun t _ acc => if x.testBit t then acc.add (Y[8 * b + t]?.getD W.zero) else acc)
    W.zero

@[expose] def frTable (Y : Array W) : Array W :=
  Array.ofFn (n := 98 * 256) fun i => frEntry Y (i.val / 256) (i.val % 256)

@[inline, expose] def frStep (t : Array W) (base : Nat) (xp xm : UInt64) (s : UInt64)
    (acc : W) : W :=
  let pb := ((xp >>> s) &&& 255).toNat
  let mb := ((xm >>> s) &&& 255).toNat
  let acc := if pb = 0 then acc else acc.add (t[base + pb]?.getD W.zero)
  if mb = 0 then acc else acc.sub (t[base + mb]?.getD W.zero)

@[inline, expose] def frLimb (t : Array W) (base : Nat) (xp xm : UInt64) (acc : W) : W :=
  let acc := frStep t base xp xm 0 acc
  let acc := frStep t (base + 256) xp xm 8 acc
  let acc := frStep t (base + 512) xp xm 16 acc
  let acc := frStep t (base + 768) xp xm 24 acc
  let acc := frStep t (base + 1024) xp xm 32 acc
  let acc := frStep t (base + 1280) xp xm 40 acc
  let acc := frStep t (base + 1536) xp xm 48 acc
  frStep t (base + 1792) xp xm 56 acc

@[expose] def frApply (t : Array W) (a : W) : W :=
  let acc := frLimb t 0 a.p0 a.m0 W.zero
  let acc := frLimb t 2048 a.p1 a.m1 acc
  let acc := frLimb t 4096 a.p2 a.m2 acc
  let acc := frLimb t 6144 a.p3 a.m3 acc
  let acc := frLimb t 8192 a.p4 a.m4 acc
  let acc := frLimb t 10240 a.p5 a.m5 acc
  let acc := frLimb t 12288 a.p6 a.m6 acc
  let acc := frLimb t 14336 a.p7 a.m7 acc
  let acc := frLimb t 16384 a.p8 a.m8 acc
  let acc := frLimb t 18432 a.p9 a.m9 acc
  let acc := frLimb t 20480 a.p10 a.m10 acc
  let acc := frLimb t 22528 a.p11 a.m11 acc
  let acc := frStep t 24576 a.p12 a.m12 0 acc
  frStep t 24832 a.p12 a.m12 8 acc

@[expose] def mulW (X Y : Array W) : Array W := X.map (frApply (frTable Y))

@[expose] def powW (d : Nat) (M : Array W) : Nat → Array W
  | 0 => idW d
  | e + 1 => mulW (powW d M e) M

@[inline, expose] def W.nz (a : W) (l : Nat) (bit : UInt64) : Bool :=
  (a.limbP l ||| a.limbM l) &&& bit != 0

@[expose] def findPiv (X : Array W) (l : Nat) (bit : UInt64) (j : Nat) : Nat :=
  if h : j < X.size then (if X[j].nz l bit then j else findPiv X l bit (j + 1)) else X.size
termination_by X.size - j

@[expose] def elimRows (X : Array W) (r l : Nat) (bit : UInt64) (pv : W) : Array W :=
  X.mapIdx fun h x =>
    if h = r then x
    else if x.limbP l &&& bit != 0 then x.sub pv
    else if x.limbM l &&& bit != 0 then x.add pv
    else x

structure RRef where
  rows : Array W
  rank : Nat
  piv : Array Nat
deriving Inhabited, DecidableEq

@[expose] def colStep (st : RRef) (c : Nat) : RRef :=
  if st.rank < st.rows.size then
    let l := c >>> 6
    let bit : UInt64 := (1 : UInt64) <<< (c &&& 63).toUInt64
    let j := findPiv st.rows l bit st.rank
    if j < st.rows.size then
      let X := st.rows.swapIfInBounds st.rank j
      let X := if (X[st.rank]?.getD W.zero).limbM l &&& bit != 0 then X.modify st.rank W.neg
        else X
      ⟨elimRows X st.rank l bit (X[st.rank]?.getD W.zero), st.rank + 1, st.piv.push c⟩
    else st
  else st

@[expose] def rref (d : Nat) (X : Array W) : RRef :=
  Nat.fold d (fun c _ st => colStep st c) ⟨X, 0, #[]⟩

@[expose] def W.zeroBelow (a : W) (c : Nat) : Bool :=
  Nat.all 13 fun l _ =>
    if 64 * (l + 1) ≤ c then (a.limbP l ||| a.limbM l) == 0
    else if 64 * l ≤ c then
      (a.limbP l ||| a.limbM l) &&& (((1 : UInt64) <<< (c - 64 * l).toUInt64) - 1) == 0
    else true

@[expose] def rrefOK (r : Nat) (F : RRef) : Bool :=
  let M := F.piv.foldl (fun M c => M.setTrit c 1) W.zero
  F.rows.size == r && F.piv.size == r && F.rank == r &&
    Nat.all r (fun k _ =>
      let c := F.piv[k]!
      let x := F.rows[k]!
      c < 781 && (k == 0 || F.piv[k - 1]! < c) && x.canon && x.zeroBelow c &&
        x.restrictEq M (W.zero.setTrit c 1))

@[inline, expose] def stepForm (t : Array W) (X : Array W) : RRef :=
  rref 781 (X.map (frApply t))

@[inline, expose] def mix (x : UInt64) : UInt64 :=
  let x := x ^^^ (x >>> 30)
  let x := x * 0xbf58476d1ce4e5b9
  let x := x ^^^ (x >>> 27)
  let x := x * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

@[expose] def W.hashFrom (h : UInt64) (a : W) : UInt64 :=
  let h := mix (h ^^^ a.p0 ^^^ (a.m0 <<< 1))
  let h := mix (h ^^^ a.p1 ^^^ (a.m1 <<< 1))
  let h := mix (h ^^^ a.p2 ^^^ (a.m2 <<< 1))
  let h := mix (h ^^^ a.p3 ^^^ (a.m3 <<< 1))
  let h := mix (h ^^^ a.p4 ^^^ (a.m4 <<< 1))
  let h := mix (h ^^^ a.p5 ^^^ (a.m5 <<< 1))
  let h := mix (h ^^^ a.p6 ^^^ (a.m6 <<< 1))
  let h := mix (h ^^^ a.p7 ^^^ (a.m7 <<< 1))
  let h := mix (h ^^^ a.p8 ^^^ (a.m8 <<< 1))
  let h := mix (h ^^^ a.p9 ^^^ (a.m9 <<< 1))
  let h := mix (h ^^^ a.p10 ^^^ (a.m10 <<< 1))
  let h := mix (h ^^^ a.p11 ^^^ (a.m11 <<< 1))
  mix (h ^^^ a.p12 ^^^ (a.m12 <<< 1))

@[expose] def hashRows (X : Array W) : UInt64 := X.foldl W.hashFrom 0x9e3779b97f4a7c15

end CFSG.Sporadic.Fi24.Native
