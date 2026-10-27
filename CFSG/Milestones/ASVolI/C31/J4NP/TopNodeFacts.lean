module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native

@[expose] def burnsideJ4NP_topKids : ℕ → List ℕ
  | 1 => [2, 3, 4, 5, 6, 7, 8, 9, 10]
  | 2 => [11, 21, 23, 27, 36, 39, 42, 44, 45, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66,
      67, 110, 111, 112, 113, 115, 116, 121, 124, 129]
  | 3 => [18, 76, 107, 117, 122, 123]
  | 4 => [19, 22, 51, 69, 78, 102, 134]
  | 7 => [30, 31, 32, 65, 77]
  | _ => []

@[expose] def burnsideJ4NP_Aff2A : Prop :=
  ∀ x ∈ Hj, x ≠ 1 → burnsideJ4NP_Is2A x → burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true

@[expose] def burnsideJ4NP_TopNodeFacts (k : ℕ) : Prop :=
  burnsideJ4NP_Aff2A → Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k →
    burnsideJ4NP_TreeStep k ∧
      ∀ k' ∈ burnsideJ4NP_topKids k,
        Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)) = treeOrd k'

theorem burnsideJ4NP_topNodeFacts_of {k : ℕ} {kids : List (ℕ × ℕ)}
    (he : burnsideJ4NP_topKids k = kids.map Prod.fst)
    (h : burnsideJ4NP_Aff2A →
      Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k →
        burnsideJ4NP_TreeStep k ∧ ∀ kd ∈ kids,
          Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep kd.1 : Set J)) = treeOrd kd.1) :
    burnsideJ4NP_TopNodeFacts k := by
  intro haff hN
  refine ⟨(h haff hN).1, fun k' hk' => ?_⟩
  rw [he, List.mem_map] at hk'
  obtain ⟨kd, hkd, rfl⟩ := hk'
  exact (h haff hN).2 kd hkd

end CFSG.ASVolI
