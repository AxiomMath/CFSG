module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.Sporadic.Schreier.Co3.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native

@[inline, expose] def pairIdx22 (i j : Nat) : Nat := 22 * i - i * (i - 1) / 2 + (j - i)

@[inline, expose] def formAt (b : ByteArray) (r : Nat) : Nat := hexAt b (65 * r) 64

@[expose] def triRows (t : Nat) : Array Nat :=
  Array.ofFn (n := 22) fun i => ofBits 22 fun j => decide (i.val ≤ j) && t.testBit (pairIdx22 i j)

@[inline, expose] def coefBit (C : Array Nat) (i j : Nat) : Bool :=
  if i = j then (C[i]?.getD 0).testBit i
  else ((C[i]?.getD 0).testBit j ^^ (C[j]?.getD 0).testBit i)

@[expose] def coefOK (C : Array Nat) (t : Nat) : Bool :=
  allLt 22 fun i => allLt 22 fun j =>
    !decide (i ≤ j) || coefBit C i j == t.testBit (pairIdx22 i j)

@[expose] def pullOK (A : Array Nat) (t t' : Nat) : Bool :=
  coefOK (mulRows 22 (transposeRows 22 A) (mulRows 22 (triRows t') A)) t

@[expose] def offDiagOK (t t' : Nat) : Bool :=
  allLt 22 fun i => allLt 22 fun j =>
    !decide (i < j) || t.testBit (pairIdx22 i j) == t'.testBit (pairIdx22 i j)

@[expose] def diagVec (t : Nat) : Nat := ofBits 22 fun i => t.testBit (pairIdx22 i i)

end CFSG.Sporadic.Schreier.Co3.Native
