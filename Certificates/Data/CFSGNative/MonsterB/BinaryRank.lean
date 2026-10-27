module

public import Certificates.Data.CFSGNative.MonsterB.BinaryFiles
public import Certificates.Data.CFSGNative.MonsterB.BinaryElim
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.Monster.B.Binary.Native

open CFSG.Monster.B.Dyadic.Native CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native

@[expose] def natFrom (b : ByteArray) (k : Nat) : Nat :=
  if k < b.size then (b.get! k).toNat + 256 * natFrom b (k + 1) else 0
termination_by b.size - k

@[expose] def rowNat (b : ByteArray) : Nat := natFrom b 0

@[expose] def transRow (m : Nat) (R : Array ByteArray) (j : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := 552) fun b => packByte fun u =>
    decide (8 * b.val + u < m) && rowBit (R[8 * b.val + u]!) j)

@[expose] def plusId (m : Nat) (R : Array ByteArray) : List Nat :=
  (List.range m).map fun i => rowNat (R[i]!) ^^^ (1 <<< i)

@[expose] def plusIdT (m : Nat) (R : Array ByteArray) : List Nat :=
  (List.range m).map fun j => rowNat (transRow m R j) ^^^ (1 <<< j)

@[expose] def fixedByAll (C : Array (Array ByteArray)) : Bool :=
  (List.range 26).all fun g => vecMulN 4371 ((C[g]!).map rowNat) fixedVector == fixedVector

@[expose] def allBelowB (b : Nat) (vs : List Nat) : Bool := vs.all fun v => decide (v < b)

@[expose] def allBelow (d : Nat) (vs : List Nat) : Bool := allBelowB (2 ^ d) vs

@[expose] def allCols (C : Array (Array ByteArray)) : List Nat :=
  (List.range 26).flatMap fun g => plusIdT 4371 (C[g]!)

@[expose] def allRows (C : Array (Array ByteArray)) : List Nat :=
  (List.range 26).flatMap fun g => plusId 4371 (C[g]!)

@[expose] def missingOnly (d q : Nat) (T : Array Nat) : Bool :=
  T.size == d && allLt d fun p => (T[p]! == 0) == (p == q)

@[expose] def fullTable (d : Nat) (T : Array Nat) : Bool :=
  T.size == d && allLt d fun p => T[p]! != 0

@[expose] def missingOpt (d q : Nat) : Option (Array Nat) → Bool
  | none => false
  | some T => missingOnly d q T

@[expose] def fullOpt (d : Nat) : Option (Array Nat) → Bool
  | none => false
  | some T => fullTable d T

@[expose] def rankOpt (d r : Nat) : Option (Array Nat) → Bool
  | none => false
  | some T => T.size == d && tableRank d T == r

@[expose] def colsOKOf (vs : List Nat) (q : Nat) : Bool :=
  allBelow 4371 vs && missingOpt 4371 q (elimTable 4371 vs)

@[expose] def rowsOKOf (vs : List Nat) : Bool :=
  allBelow 4371 vs && fullOpt 4371 (elimTable 4371 vs)

@[expose] def rankOKOf (vs : List Nat) (r : Nat) : Bool :=
  allBelow 4370 vs && rankOpt 4370 r (elimTable 4370 vs)

@[expose] def colsOK (C : Array (Array ByteArray)) (q : Nat) : Bool := colsOKOf (allCols C) q

@[expose] def rowsOK (C : Array (Array ByteArray)) : Bool := rowsOKOf (allRows C)

@[expose] def rankOK (Q : Array (Array ByteArray)) (g r : Nat) : Bool :=
  rankOKOf (plusId 4370 (Q[g]!)) r

@[expose] def qNat (Q : Array (Array ByteArray)) (g : Nat) : Array Nat := (Q[g]!).map rowNat

@[expose] def ordersOKOf (q0 q25 : Array Nat) : Bool :=
  q0.size == 4370 && q25.size == 4370 && frMul 4370 q0 q0 == idRows 4370 &&
    frMul 4370 (frMul 4370 q25 q25) q25 == idRows 4370

@[expose] def ordersOK (Q : Array (Array ByteArray)) : Bool := ordersOKOf (qNat Q 0) (qNat Q 25)

@[expose] def binaryCheck (C Q : Array (Array ByteArray)) (q : Nat) : Bool :=
  fixedByAll C && colsOK C q && rowsOK C && rankOK Q 0 1860 && rankOK Q 25 2862 && ordersOK Q

@[noinline, expose] def binaryCheckC (C : Array (Array ByteArray)) (q : Nat) : Bool :=
  binaryCheck C (allQRows (qParts C)) q

@[expose] def binaryOK (chunks q : Nat) : Bool := binaryCheckC (allCRows chunks) q

end CFSG.Monster.B.Binary.Native
