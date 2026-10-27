module

public import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def elemDag : List Rows × List Rows × Bool :=
  dag [yR, tR, zR] (Data.dagWords.map decWord)

@[expose] def aRows (i : Nat) : Rows := elemDag.1.getD (Data.elemIdx.getD i 0) one

@[expose] def eRows (b : Fin 6 → ZMod 3) : Rows :=
  ((List.finRange 6).map fun i => pow (aRows i.val) (b i).val).foldr mul one

@[expose] def f4Lo (cs : List Nat) : Nat :=
  (List.finRange 12).foldl
    (fun acc k => if cs.getD k.val 0 % 2 = 1 then acc ^^^ (1 <<< k.val) else acc) 0

@[expose] def f4Hi (cs : List Nat) : Nat :=
  (List.finRange 12).foldl
    (fun acc k => if cs.getD k.val 0 / 2 % 2 = 1 then acc ^^^ act zR (1 <<< k.val) else acc) 0

@[expose] def qNat (j : Nat) : Nat := f4Lo (Data.f4vecs.getD j []) ^^^ f4Hi (Data.f4vecs.getD j [])

@[expose] def zPow (e : Nat) (v : Nat) : Nat := Nat.iterate (act zR) e v

@[expose] def gam (j i : Nat) : Nat := (Data.eigenchars.getD j []).getD i 0

@[expose] def qCols : Array Nat := Array.ofFn (n := 24) fun k =>
  if k.val % 2 = 0 then qNat (k.val / 2) else act zR (qNat (k.val / 2))

@[expose] def qMat : Rows := transposeRows 24 qCols

@[expose] def elemCheck : Bool :=
  elemDag.2.2 &&
    (List.range 6).all (fun i => (List.range 6).all fun j =>
      mul (aRows i) (aRows j) == mul (aRows j) (aRows i)) &&
    (List.range 6).all (fun i => pow (aRows i) 3 == one)

@[expose] def eCheck : Bool :=
  decide (∀ b ∈ (Finset.univ : Finset (Fin 6 → ZMod 3)), wf (eRows b) = true) &&
    decide ((Finset.univ : Finset (Fin 6 → ZMod 3)).val.map eRows).Nodup &&
    (List.finRange 6).all fun i => eRows (Pi.single i 1) == aRows i.val

@[expose] def eigenCheck : Bool :=
  (List.range 6).all (fun i => (List.range 12).all fun j =>
      act (aRows i) (qNat j) == zPow (gam j i) (qNat j) && decide (gam j i < 3)) &&
    mul zR zR == add zR one && mul (inv qMat) qMat == one && aRows 0 == zR &&
    mul qMat (inv qMat) == one

end Native

end CFSG.Sporadic.Co1Schreier
