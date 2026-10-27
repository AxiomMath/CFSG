module

public import CFSG.Quasithin.EmptyFaithful.S146zUF0Num

public section

namespace CFSG.Quasithin.S146zU

theorem numerics_core_cond {Y : Type*} [CommGroup Y] [Finite Y] {A : Subgroup (MulAut Y)}
    {E : Subgroup Y} (hEA : ∀ a ∈ A, ∀ e ∈ E, a e ∈ E)
    (H1 : Nat.card Y ≤ Nat.card A * Nat.card A * Nat.card ↥(fixV A))
    (H2 : Nat.card A * Nat.card ↥(E ⊓ fixV A) ≤ Nat.card E)
    (H3 : Nat.card A * Nat.card ↥(cF A E) ≤ Nat.card Y)
    (H4 : Nat.card Y = Nat.card A * Nat.card A * Nat.card ↥(fixV A) →
      ∃ (D : Subgroup Y) (c : Y), Nat.card Y = Nat.card A * Nat.card D ∧
        ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c)
    (H5 : Nat.card E = Nat.card A * Nat.card ↥(E ⊓ fixV A) →
      ∀ s ∈ E, s ∉ fixV A → 4 ≤ (Set.range fun a : ↥A => (a : MulAut Y) s).ncard)
    (H5F : Nat.card Y = Nat.card A * Nat.card ↥(cF A E) →
      ∃ y₁ y₂ : Y, ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ y₁ * y₁⁻¹ ∉ E ∧ a₂ y₂ * y₂⁻¹ ∉ E ∧
        (a₁ y₁ * y₁⁻¹)⁻¹ * (a₂ y₂ * y₂⁻¹) ∉ E) :
    False := by
  obtain ⟨-, -, hY⟩ := UF0.counting_eq hEA H1 H2 H3
  obtain ⟨D, c, H4a, H4b⟩ := H4 hY
  exact numerics_core hEA H1 H2 H3 H4a H4b H5 H5F

end CFSG.Quasithin.S146zU
