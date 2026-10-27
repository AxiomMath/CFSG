module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem Tset_subset_Eset (S : Setting z E F) (a : G) : Tset S a ⊆ Eset S a := by
  intro α hα
  exact ⟨1, α, hα, by simp⟩

theorem Eset_conj_mem (S : Setting z E F) (a : G) {α : Hbar z}
    (hα : α ∈ Eset S a) (h : Hbar z) :
    h * α * h⁻¹ ∈ Eset S a := by
  obtain ⟨k, β, hβ, rfl⟩ := hα
  exact ⟨h * k, β, hβ, by group⟩

theorem Xsub_normal (S : Setting z E F) (a : G) : (Xsub S a).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (Eset_conj_mem S a hy g)
  | one => simp
  | mul x y _ _ ihx ihy =>
      rw [← conj_mul]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
      rw [← conj_inv]
      exact Subgroup.inv_mem _ ihx

theorem Xsub_le_of_Eset_le (S : Setting z E F) (a : G) {K : Subgroup (Hbar z)}
    (hK : Eset S a ⊆ K) : Xsub S a ≤ K :=
  (Subgroup.closure_le (K := K)).mpr hK

end CFSG.RankThree.GF2n.Stroth78
