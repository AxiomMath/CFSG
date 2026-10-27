module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusGeneric
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusModel

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups commutatorElement

theorem even_minus_four_actual_derived_extraction {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W = 4)
    (hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
      (ψ : W ≃ₗ[K] hermFourSpace D.σ) (ρ : SL(2, E) →* (W ≃ₗ[K] W)),
      (∀ w, hermFourForm D (ψ w) = Q w) ∧
      (∀ g w, ψ (ρ g w) = hermFourRho D g (ψ w)) ∧
      Function.Injective ρ ∧
      (∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
        ρ.range ∧
      IsSimpleGroup ρ.range ∧ Group.IsPerfect ρ.range ∧
      (¬ ∀ x y : ρ.range, x * y = y * x) ∧
      Nat.card ρ.range = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) ∧
      (ρ.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 ∧
      (ρ.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) → g ∈ ρ.range := by
  obtain ⟨E, _, _, D, ψ₀, hψ₀⟩ := exists_evenMinus_model Q hQ (n := 2) (by norm_num)
    (by omega) hts
  let ψ : W ≃ₗ[K] hermFourSpace D.σ := ψ₀.trans (hermFourCoord D)
  have hψ : ∀ w, hermFourForm D (ψ w) = Q w := fun w => by
    rw [← hψ₀ w]
    exact (hermFourIsometry D).map_app (ψ₀ w)
  let e : Q.IsometryEquiv (hermFourForm D) := { ψ with map_app' := hψ }
  obtain ⟨-, -, -, -, -, -, -, hmem, hinj, -, -, -, hJcard, hOcard, -⟩ :=
    even_minus_four_hermitian_derived_model D
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hE4 : 4 ≤ Nat.card E := by
    rw [D.card_E]
    nlinarith
  have := D.finite_E
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have : IsSimpleGroup SL(2, E) := sl2_isSimpleGroup hE4
  have : Group.IsPerfect SL(2, E) := sl2_isPerfect hE4
  have : Finite SL(2, E) := inferInstance
  have hρinj := transportHom_injective e (hermFourRho D) hinj
  have hρmem := transportHom_mem e (hermFourRho D) hmem
  have hle : (transportHom e (hermFourRho D)).range ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcardSL : Nat.card SL(2, E) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [← hJcard, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card SL(2, E) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e, hOcard, hcardSL]
  obtain ⟨hs, hp, hna, hcr, hidx, hnorm, hcomm, hodd⟩ := derived_of_index_two_model
    (TauCeti.QuadraticMap.orthogonalGroup Q) (transportHom e (hermFourRho D)) hρinj hle hcard
  exact ⟨E, inferInstance, inferInstance, D, ψ, transportHom e (hermFourRho D), hψ,
    fun g w => transportHom_apply e (hermFourRho D) g w, hρinj, hρmem, hcomm, hs, hp, hna,
    hcr.trans hcardSL, hidx, hnorm, hodd⟩

end CFSG.RankThree.PartOne
