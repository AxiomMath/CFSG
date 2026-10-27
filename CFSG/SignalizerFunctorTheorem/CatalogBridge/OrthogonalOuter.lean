module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.OuterSeries
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldOrthogonal
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoFinal

public section

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.PartOne (OuterPrimeTwoTrivial OrthogonalOuterPrimeTwoTrivial)
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem eq_or_eq_or_eq_of_card_le_two {X : Type*} [Finite X] (hX : Nat.card X ≤ 2) (a b c : X) :
    a = b ∨ a = c ∨ b = c := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hab, hac, hbc⟩ := hcon
  have : Fintype X := Fintype.ofFinite X
  have h3 : ({a, b, c} : Finset X).card = 3 := Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h4 : ({a, b, c} : Finset X).card ≤ Fintype.card X := Finset.card_le_univ _
  rw [← Nat.card_eq_fintype_card] at h4
  omega

theorem mem_or_mem_or_inv_mul_mem_of_relIndex_le_two {G : Type*} [Group G] [Finite G]
    {O D : Subgroup G} (h : O.relIndex D ≤ 2) :
    ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ∈ O ∨ d₂ ∈ O ∨ d₁⁻¹ * d₂ ∈ O := by
  intro d₁ h₁ d₂ h₂
  have hcard : Nat.card (D ⧸ O.subgroupOf D) ≤ 2 := by
    rw [← Subgroup.index_eq_card]
    exact h
  rcases eq_or_eq_or_eq_of_card_le_two hcard (QuotientGroup.mk 1) (QuotientGroup.mk ⟨d₁, h₁⟩)
    (QuotientGroup.mk ⟨d₂, h₂⟩) with h' | h' | h'
  · left
    have := QuotientGroup.eq.1 h'
    simpa [Subgroup.mem_subgroupOf] using this
  · right
    left
    have := QuotientGroup.eq.1 h'
    simpa [Subgroup.mem_subgroupOf] using this
  · right
    right
    have := QuotientGroup.eq.1 h'
    simpa [Subgroup.mem_subgroupOf] using this

theorem outerPrimeTwoTrivial_of_mulEquiv {S S' : Type} [Group S] [Group S'] (φ : S ≃* S')
    (h : OuterPrimeTwoTrivial S') : OuterPrimeTwoTrivial S := by
  intro r P Q hr hr3 hP hQ hnorm hcomm
  let Φ : Outer S ≃* Outer S' := CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ
  have h1 : Q.map Φ.toMonoidHom = ⊥ := by
    refine h r (P.map Φ.toMonoidHom) (Q.map Φ.toMonoidHom) hr hr3 (hP.map _) (hQ.map _) ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x'
      obtain ⟨x, rfl⟩ := Φ.surjective x'
      have hyx := Subgroup.mem_normalizer_iff.1 (hnorm hy) x
      have e1 : Φ.toMonoidHom y * Φ x * (Φ.toMonoidHom y)⁻¹ = Φ (y * x * y⁻¹) := by simp
      rw [e1, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
      simpa using hyx
    · rw [← Subgroup.map_commutator, hcomm]
  exact (Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).1 h1

theorem outerPrimeTwoTrivial_matrixProjectiveDerived {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hidx : (matrixProjectiveImage Q).index ≤ 3) :
    OuterPrimeTwoTrivial (matrixProjectiveDerived Q) := by
  intro r P R hr hr3 hP _ _ hcomm
  have hQv := exists_nonzero_value Q hQ
  let π : MulAut (matrixProjectiveDerived Q) →* Outer (matrixProjectiveDerived Q) :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q) := QuotientGroup.ker_mk' _
  have hIbot : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).map π = ⊥ :=
    (Subgroup.map_eq_bot_iff _).2 hker.ge
  have hDE : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩
  have hidx' : ((matrixProjectiveImage Q).map π).index ≤ 3 := by
    refine le_trans (Nat.le_of_dvd ?_ (Subgroup.index_map_dvd (matrixProjectiveImage Q) hπ)) hidx
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hEE : ⁅matrixProjectiveImage Q, matrixProjectiveImage Q⁆ ≤
      (linearConjugationHom Q).range := by
    refine Subgroup.commutator_le.2 fun e₁ he₁ e₂ he₂ => ?_
    obtain ⟨g₁, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 he₁
    obtain ⟨g₂, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 he₂
    change ⁅matrixProjectiveConjugationHom Q g₁, matrixProjectiveConjugationHom Q g₂⁆ ∈ _
    rw [← map_commutatorElement]
    refine ⟨⟨⁅g₁, g₂⁆, ?_⟩, rfl⟩
    rw [mem_linearSimilarityPairs_iff]
    change fieldProjection Q ⁅g₁, g₂⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ringAut_commute _ _
  have hEab : ⁅(matrixProjectiveImage Q).map π, (matrixProjectiveImage Q).map π⁆ ≤
      ((linearConjugationHom Q).range).map π := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hEE
  have hOE : ∀ e ∈ (matrixProjectiveImage Q).map π, ∀ o ∈ ((isometryConjugationHom Q).range).map π,
      e * o * e⁻¹ ∈ ((isometryConjugationHom Q).range).map π := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨o, ⟨A, rfl⟩, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 he
    have hmem : g * matrixIsometryInclusion Q A * g⁻¹ ∈ matrixIsometryPairs Q :=
      (matrixIsometryPairs_normal Q).conj_mem _ ⟨A, rfl⟩ g
    obtain ⟨A', hA'⟩ := hmem
    refine ⟨isometryConjugationHom Q A', ⟨A', rfl⟩, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    change π (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A')) = _
    rw [hA', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rfl
  have hA0 : 0 < Nat.card (Abelianization (matrixIsometries Q)) := Nat.card_pos
  have hO4 : Nat.card (((isometryConjugationHom Q).range).map π) ≤ 4 := by
    have h1 : Nat.card (((isometryConjugationHom Q).range).map π) ∣
        Nat.card (Abelianization (matrixIsometries Q)) := by
      rw [← Subgroup.relIndex_bot_left, ← hIbot]
      exact (relIndex_map_dvd_relIndex π _ _).trans (relIndex_inner_dvd Q)
    exact (Nat.le_of_dvd hA0 h1).trans hab
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index ≤ 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    exact Nat.gcd_le_right _ two_pos
  have hsq0 : 0 < (powMonoidHom 2 : Kˣ →* Kˣ).range.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hDO : (((isometryConjugationHom Q).range).map π).relIndex
      (((linearConjugationHom Q).range).map π) ≤ 2 := by
    refine le_trans (Nat.le_of_dvd hsq0 ?_) hsq
    exact (relIndex_map_dvd_relIndex π _ _).trans (relIndex_isometryRange_dvd Q hQv)
  exact outerSeries_trivial ((matrixProjectiveImage Q).map π)
    (((linearConjugationHom Q).range).map π) (((isometryConjugationHom Q).range).map π)
    (Subgroup.map_mono hDE) hidx' hEab hOE hO4
    (mem_or_mem_or_inv_mul_mem_of_relIndex_le_two hDO) hr hr3 hP hcomm

theorem orthogonalOuterPrimeTwoTrivial : OrthogonalOuterPrimeTwoTrivial := by
  intro S _ _ _ _ t n ℓ f ht hm
  rcases ht with rfl | rfl | rfl
  · have h0 := hm
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
    obtain ⟨hQ, hab, hidx⟩ := orthOdd_hyps hm K hK e
    exact outerPrimeTwoTrivial_of_mulEquiv (coordinateOddWitnessEquiv K e)
      (outerPrimeTwoTrivial_matrixProjectiveDerived _ hQ hab hidx)
  · have h0 := hm
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
    obtain ⟨hQ, hab, hidx⟩ := orthPlus_hyps hm K hK e
    exact outerPrimeTwoTrivial_of_mulEquiv (coordinatePlusWitnessEquiv K e)
      (outerPrimeTwoTrivial_matrixProjectiveDerived _ hQ hab hidx)
  · have hn1 : 1 ≤ n := by
      have := hm.1.2.2
      omega
    have h0 := hm
    obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
    obtain ⟨hQ, hab, hidx⟩ := orthMinus_hyps hm K hK b c hirr hn1 e
    exact outerPrimeTwoTrivial_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
      (outerPrimeTwoTrivial_matrixProjectiveDerived _ hQ hab hidx)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
