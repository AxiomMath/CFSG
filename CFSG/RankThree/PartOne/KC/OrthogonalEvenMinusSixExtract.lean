module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusGeneric
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusModel
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSix

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

theorem even_minus_six_actual_derived_extraction {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
      (ψ : W ≃ₗ[K] D.sixSpace) (ρ : D.sixSU →* (W ≃ₗ[K] W)),
      (∀ w, D.sixForm (ψ w) = Q w) ∧
      (∀ g w, ψ (ρ g w) = D.sixRho g (ψ w)) ∧
      Function.Injective ρ ∧
      (∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
        ρ.range ∧
      IsSimpleGroup ρ.range ∧ Group.IsPerfect ρ.range ∧
      (¬ ∀ x y : ρ.range, x * y = y * x) ∧
      Nat.card ρ.range =
        Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) ∧
      (ρ.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 ∧
      (ρ.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) → g ∈ ρ.range := by
  obtain ⟨E, _, _, D, ψ₀, hψ₀⟩ := exists_evenMinus_model Q hQ (n := 3) (by norm_num)
    (by omega) hts
  let ψ : W ≃ₗ[K] D.sixSpace := ψ₀.trans D.sixCoord
  have hψ : ∀ w, D.sixForm (ψ w) = Q w := fun w => by
    rw [← hψ₀ w]
    exact D.sixIsometry.map_app (ψ₀ w)
  let e : Q.IsometryEquiv D.sixForm := { ψ with map_app' := hψ }
  obtain ⟨-, -, -, -, -, -, -, hmem, hinj, -, -, -, hJcard, hOcard, -⟩ :=
    even_minus_six_unitary_derived_model D
  have := D.finite_E
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := D.sixSU_isSimpleGroup
  have := D.sixSU_isPerfect
  have : Finite D.sixSU := inferInstance
  have hρinj := transportHom_injective e D.sixRho hinj
  have hρmem := transportHom_mem e D.sixRho hmem
  have hle : (transportHom e D.sixRho).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcardS : Nat.card D.sixSU =
      Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) := by
    rw [← hJcard, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card D.sixSU := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e, hOcard, hcardS]
  obtain ⟨hs, hp, hna, hcr, hidx, hnorm, hcomm, hodd⟩ := derived_of_index_two_model
    (TauCeti.QuadraticMap.orthogonalGroup Q) (transportHom e D.sixRho) hρinj hle hcard
  exact ⟨E, inferInstance, inferInstance, D, ψ, transportHom e D.sixRho, hψ,
    fun g w => transportHom_apply e D.sixRho g w, hρinj, hρmem, hcomm, hs, hp, hna,
    hcr.trans hcardS, hidx, hnorm, hodd⟩

end CFSG.RankThree.PartOne
