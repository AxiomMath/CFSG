module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515e

variable {Γ : Type*} [Group Γ]

theorem lcal_eq_empty_of_isSolvable {X : Subgroup Γ} (hX : Group.IsSolvable X) : lcal X = ∅ := by
  ext J
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hJ
  obtain ⟨hJX, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJX)
      (Subgroup.inclusion_injective hJX)
  exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr this))

theorem mem_khat_iff_of_sol_eq_bot {X : Subgroup Γ} (h : sol X = ⊥) {x : Γ} :
    x ∈ khat X ↔ x ∈ X ∧ ∀ M ∈ lcal X, x ∈ Subgroup.normalizer (M : Set Γ) := by
  by_cases hX : Group.IsSolvable X
  · rw [khat_eq_of_isSolvable hX, lcal_eq_empty_of_isSolvable hX]
    simp
  · have hl : ltilde X = lcal X := by
      ext M
      simp [ltilde, hX, mcal_eq_lcal_of_sol_eq_bot h]
    have hk : x ∈ khat X ↔ x ∈ X ∧ ∀ M ∈ ltilde X, x ∈ Subgroup.normalizer (M : Set Γ) := by
      simp [khat, Subgroup.mem_inf, Subgroup.mem_iInf]
    rw [hk, hl]

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515e
