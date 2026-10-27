module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups commutatorElement

theorem even_minus_four_six_actual_derived_extraction {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (polarBilin Q).Nondegenerate)
    (hd : finrank K W = 4 ∨ finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, Q u ≠ 0) :
    IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      Group.IsPerfect ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (¬ ∀ x y : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆, x * y = y * x) ∧
      (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) →
        g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
      (finrank K W = 4 → ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
        (ψ : W ≃ₗ[K] hermFourSpace D.σ) (ρ : SL(2, E) →* (W ≃ₗ[K] W)),
        (∀ w, hermFourForm D (ψ w) = Q w) ∧ (∀ g w, ψ (ρ g w) = hermFourRho D g (ψ w)) ∧
        Function.Injective ρ ∧
        ρ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
        Nat.card ρ.range = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1)) ∧
      (finrank K W = 6 → ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
        (ψ : W ≃ₗ[K] D.sixSpace) (ρ : D.sixSU →* (W ≃ₗ[K] W)),
        (∀ w, D.sixForm (ψ w) = Q w) ∧ (∀ g w, ψ (ρ g w) = D.sixRho g (ψ w)) ∧
        Function.Injective ρ ∧
        ρ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
        Nat.card ρ.range =
          Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
            (Nat.card K ^ 4 - 1)) := by
  rcases hd with h4 | h6
  · have hts4 : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0 := fun U hU =>
      hts U (by rw [h4]; exact hU)
    obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, -, hcomm, hs, hp, hna, hcard, hidx, -, hodd⟩ :=
      even_minus_four_actual_derived_extraction Q hQ h4 hts4
    rw [← hcomm] at hs hp hna hidx hodd
    refine ⟨hs, hp, hna, hidx, hodd, fun _ => ⟨E, inferInstance, inferInstance, D, ψ, ρ, hψ, hρψ,
      hinj, hcomm.symm, hcard⟩, fun h => absurd h (by omega)⟩
  · have hts6 : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0 := fun U hU =>
      hts U (by rw [h6]; exact hU)
    obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, -, hcomm, hs, hp, hna, hcard, hidx, -, hodd⟩ :=
      even_minus_six_actual_derived_extraction Q hQ h6 hts6
    rw [← hcomm] at hs hp hna hidx hodd
    refine ⟨hs, hp, hna, hidx, hodd, fun h => absurd h (by omega), fun _ => ⟨E, inferInstance,
      inferInstance, D, ψ, ρ, hψ, hρψ, hinj, hcomm.symm, hcard⟩⟩

end CFSG.RankThree.PartOne
