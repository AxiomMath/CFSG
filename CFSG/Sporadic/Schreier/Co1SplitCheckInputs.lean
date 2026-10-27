module

public import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def hAmbRows : List Rows :=
  Data.ambWords.map fun w => word [aR, bR] [inv aR, inv bR] (decWord w)

@[expose] def strongDag : List Rows × List Rows × Bool :=
  dag hAmbRows (Data.strongWords.map decWord)

@[expose] def gRows (i : Nat) : Rows :=
  (Data.lowerWords.getD i []).foldl
    (fun X w => mul X (word strongDag.1 strongDag.2.1 (decWord w)))
    (word [aR, bR] [inv aR, inv bR] (decWord (Data.topWords.getD i [])))

@[expose] def zqT : Array Nat := Array.ofFn (n := 36) fun i => zPow (i.val % 3) (qNat (i.val / 3))

@[expose] def zq (e k : Nat) : Nat := zqT.getD (3 * k + e) 0

@[expose] def msSearch (X : Rows) (j : Nat) : Nat × Nat × Nat :=
  let v := act X (zq 0 j)
  let w := act X (zq 1 j)
  match (List.range 36).find? (fun i => zqT.getD i 0 == v) with
  | some i => (i / 3, i % 3, ((List.range 3).find? fun f => zq f (i / 3) == w).getD 0)
  | none => (0, 0, 0)

@[expose] def msSgn (X : Rows) (j : Nat) : Nat :=
  ((msSearch X j).2.2 + 3 - (msSearch X j).2.1) % 3

@[expose] def msOK (X : Rows) : Bool := (List.range 12).all fun j =>
  let d := msSearch X j
  let s := (d.2.2 + 3 - d.2.1) % 3
  d.1 < 12 && d.2.1 < 3 && s != 0 &&
    (List.range 3).all fun e => act X (zq e j) == zq ((d.2.1 + s * e) % 3) d.1

@[expose] def splitGens : List Rows := (List.range 6).map aRows ++ (List.range 3).map gRows

@[expose] def expVec (l : List Nat) : Fin 6 → ZMod 3 := fun k => (l.getD k.val 0 : ℕ)

@[expose] def splitCheck : Bool :=
  mul aR (inv aR) == one && mul bR (inv bR) == one && strongDag.2.2 &&
    (List.range 3).all (fun i => gRows i == (Data.liftRows.getD i []).toArray) &&
    splitGens.all (fun X => let Y := inv X; mul X Y == one && msOK X && msOK Y)

@[expose] def splitDataCheck : Bool :=
  (List.range 6).all (fun i => (List.range 12).all fun j =>
      (msSearch (aRows i) j).1 == j && msSgn (aRows i) j == 1) &&
    (List.range 2).all (fun i => (List.range 12).all fun j =>
      (msSearch (gRows i) j).1 == (Data.liftPerms.getD i []).getD j 0 &&
        msSgn (gRows i) j == (Data.liftSigns.getD i []).getD j 0) &&
    (List.range 12).all fun j => (msSearch (gRows 2) j).1 == j && msSgn (gRows 2) j == 2

@[expose] def splitConjCheck : Bool :=
  (List.range 3).all (fun i => (List.range 6).all fun j =>
      mul (mul (gRows i) (aRows j)) (inv (gRows i)) ==
        eRows (expVec ((Data.conjExps.getD i []).getD j []))) &&
    (List.range 2).all (fun i =>
      mul (mul (mul (gRows 2) (gRows i)) (inv (gRows 2))) (inv (gRows i)) ==
        eRows (expVec (Data.corrExps.getD i []))) &&
    mul (gRows 2) (gRows 2) == one && gRows 2 != one

@[expose] def zqCheck : Bool :=
  (List.range 12).all fun j => (List.range 3).all fun e => decide (zq e j < 2 ^ 24) &&
    (List.range 12).all fun k => (List.range 3).all fun f =>
      (zq e j == zq f k) == (j == k && e == f)

end Native

end CFSG.Sporadic.Co1Schreier
