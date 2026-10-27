module

public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin

structure Config15422 {D : Type} [Group D] (H₁ H₂ Z' : Subgroup D) : Prop where
  amalgam : IsGoldschmidtAmalgam H₁ H₂
  card_Z : Nat.card Z' = 4
  sq_Z : ∀ z ∈ Z', z ^ 2 = 1
  Z_le : Z' ≤ H₁ ⊓ H₂
  Z_central : Z' ≤ Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup D) : Set D)
  z₁ : ∃ z ∈ Z', z ≠ 1 ∧ z ∈ Subgroup.centralizer (H₁ : Set D)
  z₂ : ∃ z ∈ Z', z ≠ 1 ∧ z ∈ Subgroup.centralizer (H₂ : Set D)
  odd₁ : ∃ v ∈ Z', v ≠ 1 ∧ v ∈ oTwoUpper H₁
  odd₂ : ∃ v ∈ Z', v ≠ 1 ∧ v ∈ oTwoUpper H₂
  nonsolv : ¬ Group.IsSolvable D

namespace Config15422

variable {D : Type} [Group D] {H₁ H₂ Z' : Subgroup D}

theorem symm (h : Config15422 H₁ H₂ Z') : Config15422 H₂ H₁ Z' where
  amalgam := ⟨h.amalgam.toIsGoldschmidtTriple.symm, h.amalgam.pCore_eq_bot⟩
  card_Z := h.card_Z
  sq_Z := h.sq_Z
  Z_le := by rw [inf_comm]; exact h.Z_le
  Z_central := by rw [inf_comm]; exact h.Z_central
  z₁ := h.z₂
  z₂ := h.z₁
  odd₁ := h.odd₂
  odd₂ := h.odd₁
  nonsolv := h.nonsolv

end Config15422

@[expose] def IsCaseEight15422 (D : Type) [Group D] : Prop :=
  F6.IsHatSym 6 D ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ F6.IsL2FieldExt p D

end CFSG.Quasithin.EmptyFaithfulMultiple
