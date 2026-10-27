module

public import CFSG.Sporadic.Schreier.Co1SplitCheck
public import CFSG.Sporadic.Schreier.Co1LocalExtData
public import CFSG.Sporadic.Schreier.Co1RigidCert
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1LocalExtData
public meta import CFSG.Sporadic.Schreier.Co1RigidCert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def cRows (i : Nat) : Rows :=
  mul (pow (mul (mul (mul (gRows 2) (gRows i)) (inv (gRows 2))) (inv (gRows i))) 2) (gRows i)

@[expose] def compRows : List Rows := [cRows 0, cRows 1, gRows 2]

@[expose] def locRows (w : List Nat × List Nat) : Rows :=
  mul (eRows (expVec w.1)) (word compRows (compRows.map inv) (w.2.map Int.ofNat))

@[expose] def hRows (i : Nat) : Rows := locRows (Data.witLeft.getD i ([], []))

@[expose] def kRows (i : Nat) : Rows := locRows (Data.witConj.getD i ([], []))

@[expose] def qInv : Rows := inv qMat

@[expose] def hqT : Array Rows := Array.ofFn (n := 3) fun i => mul (mul qInv (hRows i.val)) qMat

@[expose] def dqT : Array Rows := Array.ofFn (n := 8) fun f => (Data.rigBasis.getD f.val []).toArray

@[expose] def dsT : Array Rows :=
  Array.ofFn (n := 8) fun f => mul (mul qMat (dqT.getD f.val one)) qInv

@[expose] def rankA : Array Nat := Data.rigRank.toArray

@[expose] def eqsA : Array (List Nat) := Data.rigEqs.toArray

@[expose] def freeA : Array (Nat × Nat) := Data.rigFree.toArray

@[expose] def zeroRows : Rows := Array.ofFn (n := 24) fun _ => 0

@[expose] def coefB (c p q : Nat) : Bool :=
  (c / 24 % 24 == p && ((hqT.getD (c / 576 % 3) one).getD q 0).testBit (c % 24)) ^^
    (q == c % 24 && ((hqT.getD (c / 576 % 3) one).getD (c / 24 % 24) 0).testBit p)

@[expose] def combB (u p q : Nat) : Bool :=
  (eqsA.getD u []).foldl (fun b c => b ^^ coefB c p q) false

@[expose] def propCheck : Bool :=
  (List.range 576).all fun u => rankA.getD u 0 == 0 ||
    (combB u (u / 24) (u % 24) && (List.range 576).all fun v =>
      v == u || decide (rankA.getD v 0 < rankA.getD u 0) || !combB u (v / 24) (v % 24))

@[expose] def freeCheck : Bool :=
  (List.range 576).all fun u => rankA.getD u 0 != 0 ||
    (List.range 8).any fun f => freeA.getD f (0, 0) == (u / 24, u % 24)

@[expose] def basisCheck : Bool :=
  (List.range 8).all fun f =>
    (List.range 3).all (fun i =>
      mul (dqT.getD f one) (hqT.getD i one) == mul (hqT.getD i one) (dqT.getD f one)) &&
    (List.range 8).all fun g =>
      ((dqT.getD f one).getD (freeA.getD g (0, 0)).1 0).testBit (freeA.getD g (0, 0)).2 ==
        (f == g)

@[expose] def rigCheck : Bool :=
  mul qMat qInv == one && (List.range 2).all (fun i => mul (cRows i) (inv (cRows i)) == one) &&
    mul (gRows 2) (inv (gRows 2)) == one &&
    (List.range 3).all (fun i => mul xR (hRows i) == mul (kRows i) xR) &&
    mul xR xR == one && pow (mul xR yR) 28 == one && aRows 1 == yR && aRows 1 != one &&
    wf (aRows 1) && wf one && freeA.size == 8 &&
    (List.range 8).all fun f => decide ((freeA.getD f (0, 0)).1 < 24) &&
      decide ((freeA.getD f (0, 0)).2 < 24)

@[expose] def candRows (ε : Fin 8 → Bool) : Rows :=
  (List.finRange 8).foldl (fun R f => if ε f then add R (dsT.getD f.val one) else R) zeroRows

@[expose] def candOK (ε : Fin 8 → Bool) : Bool :=
  wf (mul (mul xR (candRows ε)) (mul xR (candRows ε))) &&
    wf (pow (mul (mul xR (candRows ε)) yR) 28) &&
    (mul (mul xR (candRows ε)) (mul xR (candRows ε)) != one ||
      pow (mul (mul xR (candRows ε)) yR) 28 != one || candRows ε == one)

end Native

end CFSG.Sporadic.Co1Schreier
