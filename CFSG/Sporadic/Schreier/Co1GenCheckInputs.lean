
module

public import CFSG.Sporadic.Schreier.Co1RigidCheckBase
public import Std.Data.HashSet
public meta import CFSG.Sporadic.Schreier.Co1RigidCheckBase
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1LocalExtData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def extInitRows : List Rows :=
  [aRows 0, aRows 1, aRows 2, aRows 3, aRows 4, aRows 5, cRows 0, cRows 1, gRows 2, xR]

@[expose] def extDag : List Rows × List Rows × Bool := dag extInitRows Data.genDerivs

@[expose] def extColsT : Array Rows :=
  Array.ofFn (n := 93) fun j => transposeRows 24 (extDag.1.getD j.val one)

@[expose] def canon (q v : Nat) : Nat := min v (v ^^^ q)

@[expose] def stepV (q g v : Nat) : Nat := canon q (vecMulN 24 (extColsT.getD g #[]) v)

@[expose] def bfs (q : Nat) (gens : List Nat) (root bound : Nat) : Array (Nat × Nat × Nat) :=
  Id.run do
    let mut seen : Std.HashSet Nat := (Std.HashSet.emptyWithCapacity 200000).insert root
    let mut out : Array (Nat × Nat × Nat) := #[(root, 0, 0)]
    for i in [0:bound] do
      if h : i < out.size then
        let v := out[i].1
        for g in gens do
          let w := stepV q g v
          if !seen.contains w then
            seen := seen.insert w
            out := out.push (w, i, g)
    return out

@[expose] def strictSorted : List Nat → Bool
  | a :: b :: r => decide (a < b) && strictSorted (b :: r)
  | _ => true

@[expose] def treeOK (q : Nat) (gens : List Nat) (root n : Nat) (t : Array (Nat × Nat × Nat)) :
    Bool :=
  t.size == n && (t.getD 0 (0, 0, 0)).1 == root &&
    (List.range n).all (fun m => decide ((t.getD m (0, 0, 0)).1 < 2 ^ 24) &&
      canon q (t.getD m (0, 0, 0)).1 == (t.getD m (0, 0, 0)).1 &&
      (m == 0 || (decide ((t.getD m (0, 0, 0)).2.1 < m) && gens.contains (t.getD m (0, 0, 0)).2.2 &&
        (t.getD m (0, 0, 0)).1 ==
          stepV q (t.getD m (0, 0, 0)).2.2 (t.getD (t.getD m (0, 0, 0)).2.1 (0, 0, 0)).1))) &&
    strictSorted ((t.toList.map (·.1)).mergeSort fun a b => decide (a ≤ b))

@[expose] def towerB (i : Nat) : Nat := Data.towerBase.getD i 0

@[expose] def towerQ (i : Nat) : Nat := Data.towerQuot.getD i 0

@[expose] def towerJ (i : Nat) : List Nat := Data.towerGens.getD i []

@[expose] def towerN (i : Nat) : Nat := Data.towerSizes.getD i 0

@[expose] def towerTree (i : Nat) : Array (Nat × Nat × Nat) :=
  bfs (towerQ i) (towerJ i) (towerB i) 100000

@[expose] def fixOK (i : Nat) : Bool :=
  (towerJ i).all fun j => decide (j < 93) &&
    vecMulN 24 (extColsT.getD j #[]) (towerQ i) == towerQ i &&
    (List.range i).all fun l => vecMulN 24 (extColsT.getD j #[]) (towerQ l) == towerQ l &&
      (vecMulN 24 (extColsT.getD j #[]) (towerB l) == towerB l ||
        vecMulN 24 (extColsT.getD j #[]) (towerB l) == towerB l ^^^ towerQ l)

@[expose] def genCheck : Bool :=
  extDag.2.2 && extDag.1.length == 93 &&
    (List.range 7).all fun i => decide (towerB i < 2 ^ 24) && decide (towerQ i < 2 ^ 24) &&
      fixOK i && treeOK (towerQ i) (towerJ i) (towerB i) (towerN i) (towerTree i)

end Native

end CFSG.Sporadic.Co1Schreier
