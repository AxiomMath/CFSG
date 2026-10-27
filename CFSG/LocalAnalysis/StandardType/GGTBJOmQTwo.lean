module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.Quasithin.Background.C118BridgeAlg
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.Quasithin.Background.C1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

open Module QuadraticMap
open scoped commutatorElement

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

private theorem tbjQ2Aux_isSolvable_of_prime_dvd {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = a ∨ r = b) : Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := a) (b := b))
  intro r hr
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)

theorem tbjQ2_isSolvable_orthogonalGroup_split_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate) (h4 : finrank K W = 4)
    (hsplit : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  classical
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun g : W ≃ₗ[K] W => g.toEquiv)
      (fun g h hgh => LinearEquiv.ext fun x => by
        simpa using congrArg (fun e : W ≃ W => e x) hgh)
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup R) := inferInstance
  have hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨ finrank K W = 5)) ∨
      (Odd (Nat.card K) ∧ finrank K W = 6 ∧
        ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) ∨
      (finrank K W = 4 ∧
        ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) :=
    Or.inr (Or.inr ⟨h4, hsplit⟩)
  have hcov :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      R hR hcase
  have hprime := (hcov.1 (Or.inr ⟨⟨h4, hsplit⟩, Or.inl hK2⟩)).1
  exact tbjQ2Aux_isSolvable_of_prime_dvd hprime

private theorem tbjQ2Aux_exists_unit_sq {K : Type} [Field K] [Finite K] [CharP K 2]
    (δ : Kˣ) : ∃ c : Kˣ, c ^ 2 = δ := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (δ : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, pow_two])⟩

private theorem tbjQ2Aux_rho_mem_specialImage {K : Type} [Field K] [Finite K] [CharP K 2]
    (z : equalDeterminants K) : rho z ∈ specialImage K := by
  obtain ⟨c, hc⟩ := tbjQ2Aux_exists_unit_sq (commonDeterminant z)⁻¹
  have hdet : commonDeterminant (scalarPair c) = c ^ 2 := by
    apply Units.ext
    simp [commonDeterminant, scalarPair, Matrix.GeneralLinearGroup.det, pow_two]
  have h1 : commonDeterminant (z * scalarPair c) = 1 := by
    rw [map_mul, hdet, hc, mul_inv_cancel]
  have h2 := rho_mem_specialImage_of_commonDeterminant (z * scalarPair c) h1
  rwa [map_mul, rho_scalarPair, mul_one] at h2

private theorem tbjQ2Aux_sl2_sq_mem_commutator {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      A ^ 2 ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK2
  obtain ⟨t, ht3, hcomm⟩ := CFSG.Quasithin.exists_commutator_eq_zpowers (F := K) hF
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
    norm_num
  have hz3 : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht3]
  have hcardC : Nat.card (commutator (Matrix.SpecialLinearGroup (Fin 2) K)) = 3 := by
    rw [hcomm, hz3]
  have hidx : (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).index = 2 := by
    have h := Subgroup.card_mul_index (commutator (Matrix.SpecialLinearGroup (Fin 2) K))
    rw [hcardC, hcardSL] at h
    omega
  intro A
  have h := Subgroup.pow_index_mem (commutator (Matrix.SpecialLinearGroup (Fin 2) K)) A
  rwa [hidx] at h

private theorem tbjQ2Aux_rho_sq_mem_commutator {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (z : equalDeterminants K) :
    (rho z) ^ 2 ∈ commutator (DeterminantIsometries K) := by
  classical
  have hmem : rho z ∈ specialImage K := tbjQ2Aux_rho_mem_specialImage z
  obtain ⟨w, hw⟩ := hmem
  rw [← hw]
  rw [← map_pow]
  have hSL := tbjQ2Aux_sl2_sq_mem_commutator hK2
  have hw2 : w ^ 2 ∈
      commutator (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
    obtain ⟨A, B⟩ := w
    have hA : A ^ 2 ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) K) := hSL A
    have hB : B ^ 2 ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) K) := hSL B
    have hprod : commutator (Matrix.SpecialLinearGroup (Fin 2) K ×
          Matrix.SpecialLinearGroup (Fin 2) K) =
        (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).prod
          (commutator (Matrix.SpecialLinearGroup (Fin 2) K)) := by
      change ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
            Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ =
          Subgroup.prod ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆
            ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆
      rw [← Subgroup.top_prod_top]
      exact Subgroup.commutator_prod_prod
        (H₁ := (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))) (H₂ := ⊤) ⊤ ⊤
    have hp : ((A, B) : Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K) ^ 2 = (A ^ 2, B ^ 2) := rfl
    rw [hp, hprod]
    exact ⟨hA, hB⟩
  have hmap : Subgroup.map (specialRho (K := K))
        (commutator (Matrix.SpecialLinearGroup (Fin 2) K ×
          Matrix.SpecialLinearGroup (Fin 2) K)) ≤
      commutator (DeterminantIsometries K) := by
    change Subgroup.map (specialRho (K := K))
        ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
          Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ ≤
      commutator (DeterminantIsometries K)
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap (Subgroup.mem_map_of_mem (specialRho (K := K)) hw2)

private theorem tbjQ2Aux_det_sq_mem_commutator {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (g : DeterminantIsometries K) :
    g ^ 2 ∈ commutator (DeterminantIsometries K) := by
  classical
  obtain ⟨z, hz | hz⟩ := determinant_isometry_exhaustion g
  · rw [hz]
    exact tbjQ2Aux_rho_sq_mem_commutator hK2 z
  · rw [hz]
    have hτ : tau (K := K) * tau (K := K) = 1 := tau_mul_tau (K := K)
    have hτinv : (tau (K := K))⁻¹ = tau (K := K) := inv_eq_of_mul_eq_one_right hτ
    have hsq : (tau * rho z * tau) ^ 2 = tau * (rho z * rho z) * tau := by
      rw [pow_two]
      calc (tau * rho z * tau) * (tau * rho z * tau)
          = tau * rho z * (tau * tau) * rho z * tau := by group
        _ = tau * rho z * 1 * rho z * tau := by rw [hτ]
        _ = tau * (rho z * rho z) * tau := by group
    have hg2 : (rho z * tau) ^ 2 =
        ⁅rho z, tau⁆ * (tau * rho z * tau) ^ 2 := by
      rw [commutatorElement_def, hτinv, hsq]
      have hre : (rho z * tau * (rho z)⁻¹ * tau) * (tau * (rho z * rho z) * tau)
          = rho z * tau * (rho z)⁻¹ * (tau * tau) * (rho z * rho z) * tau := by
        group
      rw [hre, hτ, mul_one]
      rw [pow_two]
      group
    rw [hg2]
    refine (commutator (DeterminantIsometries K)).mul_mem ?_ ?_
    · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · rw [tau_rho_tau]
      exact tbjQ2Aux_rho_sq_mem_commutator hK2 (transposePair z)

theorem tbjQ2_mem_commutator_of_pow_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate) (h4 : finrank K W = 4)
    (hsplit : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)} (hg : g ^ p = 1) :
    g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  classical
  by_cases hg1 : g = 1
  · rw [hg1]
    exact Subgroup.one_mem _
  · have hord : orderOf g = p := by
      rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf g)
        (orderOf_dvd_of_pow_eq_one hg) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    obtain ⟨S, hSdim, hSQ⟩ := hsplit
    obtain ⟨-, e, -, -, -⟩ := split_four_determinant_form_isometry R hR h4 S hSdim hSQ
    have hsq : ∀ x : ↥(TauCeti.QuadraticMap.orthogonalGroup R),
        x ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      CFSG.LocalAnalysis.ComponentInitial.sq_mem_commutator_of_mulEquiv e
        (tbjQ2Aux_det_sq_mem_commutator hK2)
    have hP : IsPGroup 2 (↥(TauCeti.QuadraticMap.orthogonalGroup R) ⧸
        commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
      CFSG.LocalAnalysis.ComponentInitial.isPGroup_two_of_forall_sq_mem hsq
    exact CFSG.LocalAnalysis.ComponentInitial.mem_of_isPGroup_two_of_orderOf_prime
      (N := commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) hP hp hp2 hord

end OrthTorus

end CFSG.StandardType

end
