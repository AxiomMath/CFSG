module

public import Mathlib

public section

namespace CFSG

namespace M23

open scoped Pointwise

@[expose] def evalGroupWord {G : Type*} [Group G] {n : ℕ} (S : Fin n → G) :
    List (Fin n × Bool) → G
  | [] => 1
  | (i, inv) :: w => (if inv then (S i)⁻¹ else S i) * evalGroupWord S w

lemma evalGroupWord_mem_closure {G : Type*} [Group G] {n : ℕ} (S : Fin n → G)
    (w : List (Fin n × Bool)) :
    evalGroupWord S w ∈ Subgroup.closure (Set.range S) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons q w ih =>
      rcases q with ⟨i, inv⟩
      simp only [evalGroupWord]
      split
      · exact Subgroup.mul_mem _
          (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)) ih
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) ih

end M23

end CFSG
