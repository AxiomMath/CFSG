module

public import TauCeti.FieldTheory.Finite.MinpolyOrbit

public section

namespace CFSG.StandardType.GGK0LQ

theorem hAlg_of_isAlgebraic {Ω : Type} [Field Ω] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (c : Ω) : ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c := by
  have hint : IsIntegral (ZMod 2) c := Algebra.IsIntegral.isIntegral c
  refine ⟨(minpoly (ZMod 2) c).natDegree, minpoly.natDegree_pos hint, ?_⟩
  simpa [ZMod.card] using TauCeti.FiniteField.pow_card_pow_natDegree_minpoly (ZMod 2) hint

theorem hAlg_algebraicClosure (c : AlgebraicClosure (ZMod 2)) :
    ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c :=
  hAlg_of_isAlgebraic c

end CFSG.StandardType.GGK0LQ

end
