module

public import CFSG.Quasithin.H13.A6S13834F

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Quasithin

@[expose] def g5G1 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | Perm.sign σ = 1 ∧ ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))}
  mul_mem' := by
    rintro σ τ ⟨hs, hσ⟩ ⟨ht, hτ⟩
    refine ⟨by rw [map_mul, hs, ht, one_mul], ?_⟩
    simp only [Perm.mul_apply]
    rcases hτ with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> rw [h4, h5] <;>
      rcases hσ with ⟨g4, g5⟩ | ⟨g4, g5⟩ <;> simp [g4, g5]
  one_mem' := ⟨map_one _, Or.inl ⟨rfl, rfl⟩⟩
  inv_mem' := by
    rintro σ ⟨hs, hσ⟩
    refine ⟨by rw [map_inv, hs, inv_one], ?_⟩
    rcases hσ with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · exact Or.inl ⟨Perm.inv_eq_iff_eq.mpr h4.symm, Perm.inv_eq_iff_eq.mpr h5.symm⟩
    · exact Or.inr ⟨Perm.inv_eq_iff_eq.mpr h5.symm, Perm.inv_eq_iff_eq.mpr h4.symm⟩

@[expose] def StmtG52 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A B Y : Subgroup X) (ρ : ↥Y →* Perm (Fin 6)),
    B ≤ A → A ≤ Subgroup.normalizer (B : Set X) → (∀ a ∈ A, a * a ∈ B) →
    (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) →
    Y ≤ Subgroup.normalizer (A : Set X) → Y ≤ Subgroup.normalizer (B : Set X) →
    Function.Surjective ρ →
    (∀ y : ↥Y, ρ y = 1 → ∀ a ∈ A, (y : X) * a * (y : X)⁻¹ * a⁻¹ ∈ B) → B < A →
    (∀ W : Subgroup X, B ≤ W → W ≤ A → Y ≤ Subgroup.normalizer (W : Set X) → W = B ∨ W = A) →
    (∃ W : Subgroup X, B ≤ W ∧ W ≤ A ∧ B.relIndex W = 4 ∧
      ∀ y : ↥Y, ρ y ∈ g5G1 → (y : X) ∈ Subgroup.normalizer (W : Set X)) →
    (∃ W : Subgroup X, B ≤ W ∧ W ≤ A ∧ B.relIndex W = 4 ∧
      ∀ y : ↥Y, ρ y ∈ cA6 → (y : X) ∈ Subgroup.normalizer (W : Set X)) →
    B.relIndex A = 2 ^ 16 ∧
      (∀ y : ↥Y, (ρ y).IsSwap →
        (centralizerMod B A (Subgroup.zpowers (y : X))).relIndex A = 2 ^ 8) ∧
      ∀ y : ↥Y, ρ y ^ 3 = 1 → ρ y ≠ 1 →
        (centralizerMod B A (Subgroup.zpowers (y : X))).relIndex A = 2 ^ 12

end CFSG.Quasithin.H13.A6
