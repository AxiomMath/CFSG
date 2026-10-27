module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.SzVB

theorem card_range_le_index_mul {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A →* B)
    (D : Subgroup A) (T : Subgroup B) (hD : ∀ d ∈ D, φ d ∈ T) :
    Nat.card φ.range ≤ D.index * Nat.card T := by
  classical
  let f : (A ⧸ D) × T → B := fun p => φ p.1.out * (p.2 : B)
  have hcover : (φ.range : Set B) ⊆ Set.range f := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D a
    refine ⟨((a : A ⧸ D), ⟨φ (h : A)⁻¹, ?_⟩), ?_⟩
    · exact hD _ (D.inv_mem h.2)
    · show φ (a : A ⧸ D).out * φ (h : A)⁻¹ = φ a
      rw [hh, ← map_mul, mul_assoc, mul_inv_cancel, mul_one]
  calc Nat.card φ.range
      = Nat.card (φ.range : Set B) := rfl
    _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hcover
    _ ≤ Nat.card ((A ⧸ D) × T) :=
        Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = D.index * Nat.card T := by rw [Nat.card_prod, Subgroup.index_eq_card]

end CFSG.Quasithin.SzVB
