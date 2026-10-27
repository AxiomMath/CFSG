module

public import CFSG.LocalAnalysis.StandardType.GGHalfX0Bridge
public import CFSG.LocalAnalysis.StandardType.GGHalfX0Data
import CFSG.LocalAnalysis.StandardType.GGHalfX0SubOrbitK

public section

namespace CFSG.StandardType

@[expose] def ggHalfX0J0GensBits : List (List ℕ) :=
  ggHalfX0J0Idx.map ggHalfRootBits

@[expose] def ggHalfX0GensBits (D : GGHalfX0Data) : List (List ℕ) :=
  let r := ggHalfWordBits D.rWord
  ggHalfX0J0GensBits ++ (List.range 12).map fun i =>
    ggHalfMulBits (ggHalfMulBits r (ggHalfX0J0GensBits.getD i ggHalfIdBits)) r

@[expose] def ggHalfX0MatOfGens (gens : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldl (fun A i => ggHalfMulBits A (gens.getD i ggHalfIdBits)) ggHalfIdBits

@[expose] def ggHalfX0MatPow (A : List ℕ) : ℕ → List ℕ
  | 0 => ggHalfIdBits
  | n + 1 => ggHalfMulBits (ggHalfX0MatPow A n) A

inductive GGHalfX0BST where
  | leaf : GGHalfX0BST
  | node : GGHalfX0BST → ℕ → GGHalfX0BST → GGHalfX0BST

@[expose] def ggHalfX0BSTInsertCheck : GGHalfX0BST → ℕ → Option GGHalfX0BST
  | .leaf, a => some (.node .leaf a .leaf)
  | .node l x r, a =>
    if a < x then
      match ggHalfX0BSTInsertCheck l a with
      | none => none
      | some l' => some (.node l' x r)
    else if x < a then
      match ggHalfX0BSTInsertCheck r a with
      | none => none
      | some r' => some (.node l x r')
    else none

@[expose] def ggHalfX0CheckNodupAux : GGHalfX0BST → List ℕ → Bool
  | _, [] => true
  | t, v :: l =>
    match ggHalfX0BSTInsertCheck t v with
    | none => false
    | some t' => ggHalfX0CheckNodupAux t' l

@[expose] def ggHalfX0CheckNodup (l : List ℕ) : Bool :=
  ggHalfX0CheckNodupAux .leaf l

@[expose] def ggHalfX0CheckNodupLenAux : GGHalfX0BST → List ℕ → ℕ → Bool
  | _, [], 0 => true
  | _, [], _ + 1 => false
  | _, _ :: _, 0 => false
  | t, v :: l, n + 1 =>
    match ggHalfX0BSTInsertCheck t v with
    | none => false
    | some t' => ggHalfX0CheckNodupLenAux t' l n

@[expose] def ggHalfX0CheckDistinctLength (l : List ℕ) (n : ℕ) : Bool :=
  ggHalfX0CheckNodupLenAux .leaf l n

@[expose] def ggHalfX0SpanMasks : List ℕ → List ℕ
  | [] => [0]
  | v :: vs => let s := ggHalfX0SpanMasks vs; (s.map fun x => x ^^^ v) ++ s

@[expose] def ggHalfX0Pack : List ℕ → ℕ
  | [] => 0
  | v :: vs => ggHalfX0Pack vs * 2 ^ 27 + v

@[expose] def ggHalfX0Insert : ℕ → List ℕ → List ℕ
  | a, [] => [a]
  | a, b :: l => if a ≤ b then a :: b :: l else b :: ggHalfX0Insert a l

@[expose] def ggHalfX0InsertSort : List ℕ → List ℕ
  | [] => []
  | a :: l => ggHalfX0Insert a (ggHalfX0InsertSort l)

@[expose] def ggHalfX0SubKeyOfBasis (basis : List ℕ) : ℕ :=
  ggHalfX0Pack (ggHalfX0InsertSort (ggHalfX0SpanMasks basis))

@[expose] def ggHalfX0SubBasesAux (gens : List (List ℕ)) :
    List (List ℕ) → ℕ → List ℕ → List (List ℕ)
  | acc, i, [] => acc.reverse
  | acc, i, t :: ts =>
    let par := t / 24
    let gen := t % 24
    let p := acc.getD (i - 1 - par) []
    ggHalfX0SubBasesAux gens
      (p.map (fun b => ggHalfApplyBits (gens.getD gen ggHalfIdBits) b) :: acc) (i + 1) ts

@[expose] def ggHalfX0SubBases (D : GGHalfX0Data) : List (List ℕ) :=
  ggHalfX0SubBasesAux (ggHalfX0GensBits D) [ggHalfX0W0] 1 D.tree.tail

@[expose] def ggHalfX0SubKeys (D : GGHalfX0Data) : List ℕ :=
  (ggHalfX0SubBases D).map ggHalfX0SubKeyOfBasis

@[expose] def ggHalfX0CheckSubOrbit (D : GGHalfX0Data) : Bool :=
  ggHalfX0CheckDistinctLength (ggHalfX0SubKeys D) 1632 &&
  (ggHalfX0SubBases D).all (fun b => ggHalfX0CheckNodup (ggHalfX0SpanMasks b))

set_option maxHeartbeats 2000000 in
theorem ggHalfX0CheckSubOrbit_P : ggHalfX0CheckSubOrbit ggHalfX0DataP = true := by
  have hG : (ggHalfX0GensBits ggHalfX0DataP == (List.range 24).map (GGHalfX0K.gK GGHalfX0K.gensP)) =
      true := by decide +kernel
  have hn : ggHalfX0DataP.tree.tail.length + 1 = 1632 := by decide +kernel
  have hW : GGHalfX0K.rbK GGHalfX0K.basesP 0 = ggHalfX0W0 := by decide +kernel
  have hs : GGHalfX0K.stepsK GGHalfX0K.gensP GGHalfX0K.basesP ggHalfX0DataP.tree.tail 1 = true := by
    decide +kernel
  have hR : ggHalfX0SubBasesAux (ggHalfX0GensBits ggHalfX0DataP) [ggHalfX0W0] 1
      ggHalfX0DataP.tree.tail = (List.range 1632).map (GGHalfX0K.rbK GGHalfX0K.basesP) :=
    GGHalfX0K.subBases_eq (ggHalfX0GensBits ggHalfX0DataP) GGHalfX0K.gensP GGHalfX0K.basesP 1632
      ggHalfX0W0 ggHalfX0DataP.tree.tail (ggHalfX0SubBasesAux (ggHalfX0GensBits ggHalfX0DataP))
      (fun _ _ => rfl) (fun _ _ _ _ => rfl) (eq_of_beq hG) hn hW hs
  have hK : (ggHalfX0CheckDistinctLength
      (((List.range 1632).map (GGHalfX0K.rbK GGHalfX0K.basesP)).map ggHalfX0SubKeyOfBasis) 1632 &&
    ((List.range 1632).map (GGHalfX0K.rbK GGHalfX0K.basesP)).all fun b =>
      ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true := by
    decide +kernel
  have key : ∀ L : List (List ℕ), ggHalfX0SubBases ggHalfX0DataP = L →
      (ggHalfX0CheckDistinctLength (L.map ggHalfX0SubKeyOfBasis) 1632 &&
        L.all fun b => ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true →
      ggHalfX0CheckSubOrbit ggHalfX0DataP = true := by
    intro L hL h
    rw [ggHalfX0CheckSubOrbit, ggHalfX0SubKeys, hL]
    exact h
  exact key _ hR hK
set_option maxHeartbeats 2000000 in
theorem ggHalfX0CheckSubOrbit_N : ggHalfX0CheckSubOrbit ggHalfX0DataN = true := by
  have hG : (ggHalfX0GensBits ggHalfX0DataN == (List.range 24).map (GGHalfX0K.gK GGHalfX0K.gensN)) =
      true := by decide +kernel
  have hn : ggHalfX0DataN.tree.tail.length + 1 = 1632 := by decide +kernel
  have hW : GGHalfX0K.rbK GGHalfX0K.basesN 0 = ggHalfX0W0 := by decide +kernel
  have hs : GGHalfX0K.stepsK GGHalfX0K.gensN GGHalfX0K.basesN ggHalfX0DataN.tree.tail 1 = true := by
    decide +kernel
  have hR : ggHalfX0SubBasesAux (ggHalfX0GensBits ggHalfX0DataN) [ggHalfX0W0] 1
      ggHalfX0DataN.tree.tail = (List.range 1632).map (GGHalfX0K.rbK GGHalfX0K.basesN) :=
    GGHalfX0K.subBases_eq (ggHalfX0GensBits ggHalfX0DataN) GGHalfX0K.gensN GGHalfX0K.basesN 1632
      ggHalfX0W0 ggHalfX0DataN.tree.tail (ggHalfX0SubBasesAux (ggHalfX0GensBits ggHalfX0DataN))
      (fun _ _ => rfl) (fun _ _ _ _ => rfl) (eq_of_beq hG) hn hW hs
  have hK : (ggHalfX0CheckDistinctLength
      (((List.range 1632).map (GGHalfX0K.rbK GGHalfX0K.basesN)).map ggHalfX0SubKeyOfBasis) 1632 &&
    ((List.range 1632).map (GGHalfX0K.rbK GGHalfX0K.basesN)).all fun b =>
      ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true := by
    decide +kernel
  have key : ∀ L : List (List ℕ), ggHalfX0SubBases ggHalfX0DataN = L →
      (ggHalfX0CheckDistinctLength (L.map ggHalfX0SubKeyOfBasis) 1632 &&
        L.all fun b => ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true →
      ggHalfX0CheckSubOrbit ggHalfX0DataN = true := by
    intro L hL h
    rw [ggHalfX0CheckSubOrbit, ggHalfX0SubKeys, hL]
    exact h
  exact key _ hR hK

end CFSG.StandardType

end
