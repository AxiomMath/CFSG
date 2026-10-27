module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementCoprime
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullOddCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem pairConfinement_odd_supplement_centralizes
    (L M X : Subgroup G) (hXL : X ≤ L)
    (hnormal : ((L ⊓ M).subgroupOf L).Normal)
    (hindex : (L ⊓ M).relIndex L = 2) (hXodd : Odd (Nat.card X)) : X ≤ M := by
  let : ((L ⊓ M).subgroupOf L).Normal := hnormal
  have hodd : Odd (Nat.card (X.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv]
    exact hXodd
  have hsub := invertedHull_odd_subgroup_le_index_two ((L ⊓ M).subgroupOf L)
    hindex (X.subgroupOf L) hodd
  intro x hx
  exact (hsub (show (⟨x, hXL hx⟩ : L) ∈ X.subgroupOf L from hx)).2

theorem pairConfinement_p_actor_coprime [Finite G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (V R : Subgroup G) (hV : IsPGroup p V)
    (hRodd : Odd (Nat.card R)) (hRcop : Nat.Coprime p (Nat.card R)) :
    Odd (Nat.card V) ∧ Nat.Coprime (2 * Nat.card V) (Nat.card R) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hcard⟩ := hV.exists_card_eq
  rw [hcard]
  exact ⟨hpodd.pow, hRodd.coprime_two_left.mul_left (hRcop.pow_left k)⟩

variable [Finite G]

theorem pairConfinement_intersection_centralizer_fixed
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (X : Subgroup G) (hXH : X ≤ H)
    (hXM : X ≤ Subgroup.centralizer (minimalLocalFailureInvertedSet P z))
    (hcomm : ⁅Subgroup.zpowers z, H ⊓ minimalLocalFailureInvertedOvergroup P z⁆ ≤ X)
    (s : G) (hsclass : s ∈ involutionPointClass z)
    (hsA : s ∈ minimalLocalFailureInvertedOvergroup P z)
    (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (gamma : pointRightCosetSpace H) (hgamma : pointRightCosetMul H gamma s = gamma) :
    (H ⊓ rightConjugate H s) ⊓
      Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤
        rightCosetStabilizer H gamma := by
  let I := minimalLocalFailureInvertedSet P z
  let M := Subgroup.centralizer I
  let A := minimalLocalFailureInvertedOvergroup P z
  let D := H ⊓ rightConjugate H s
  let Y := D ⊓ M
  have hXY : X ≤ Y := le_inf
    (le_inf hXH (normalized_subgroup_le_right_conjugate_overgroup X H s hXH hsX)) hXM
  have hYA : Y ≤ H ⊓ A := le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans (le_sup_left : M ≤ A))
  have hzY : z ∈ Subgroup.normalizer (Y : Set G) := by
    apply (Subgroup.zpowers_le.mp)
    apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
    exact (Subgroup.commutator_mono_right hYA).trans (hcomm.trans hXY)
  have hYz : rightConjugate Y z = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (Y : Set G)).inv_mem hzY)
  have hsD : s ∈ Subgroup.normalizer (D : Set G) :=
    CFSG.BenderSuzuki.inf_rightConjugate_mem_normalizer_of_isInvolution H
      ((orderOf_eq_prime_iff.mp
        (order_two_of_mem_pointClass h.local_datum.distinguished_order hsclass)).symm)
  have hIM : Subgroup.normalizer I ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer I)).mp inferInstance
  have hsM : s ∈ Subgroup.normalizer (M : Set G) :=
    hIM (invertedHull_overgroup_normalizes_set P z h.local_datum.distinguished_order hsA)
  have hsY : s ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hsD, hsM⟩
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  exact ((involution_point_invariant_subgroup_normalizer_fixed_points h.local_datum
    S hzS hzcenter Y (inf_le_left.trans inf_le_left) hYz ⟨hsclass, hsY⟩).2
      gamma hgamma).2

theorem pairConfinement_theta_escape_contradiction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (X : Subgroup G) (hXH : X ≤ H)
    (hXM : X ≤ Subgroup.centralizer (minimalLocalFailureInvertedSet P z))
    (hcomm : ⁅Subgroup.zpowers z, H ⊓ minimalLocalFailureInvertedOvergroup P z⁆ ≤ X)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (s : G) (hsclass : s ∈ involutionPointClass z)
    (hsA : s ∈ minimalLocalFailureInvertedOvergroup P z)
    (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (gamma : pointRightCosetSpace H) (hgamma : pointRightCosetMul H gamma s = gamma)
    (hV : IsPGroup p (minimalLocalFailurePairConfinementClosure P z))
    (hVgamma : minimalLocalFailurePairConfinementClosure P z ≤ rightCosetStabilizer H gamma)
    (hVD : minimalLocalFailurePairConfinementClosure P z ≤ H ⊓ rightConjugate H s)
    (hsinvert : ∀ x ∈ minimalLocalFailureInvertedSet P z, rightConjugateElem x s = x⁻¹)
    (hescape : ¬ minimalLocalFailurePairConfinementTheta p (H ⊓ rightConjugate H s) ≤
      rightCosetStabilizer H gamma) : False := by
  let V := minimalLocalFailurePairConfinementClosure P z
  let D := H ⊓ rightConjugate H s
  let R := minimalLocalFailurePairConfinementTheta p D
  let J := rightCosetStabilizer H gamma
  have hsorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hsclass
  have hsV := pairConfinement_closure_normalizer P z h.local_datum.distinguished_order hsA
  have hsR : s ∈ Subgroup.normalizer (R : Set G) := pairConfinement_theta_normalizer p D
    (CFSG.BenderSuzuki.inf_rightConjugate_mem_normalizer_of_isInvolution H
      (orderOf_eq_prime_iff.mp hsorder).symm)
  obtain ⟨hRodd, hRcop⟩ := pairConfinement_theta_order p hp D
  obtain ⟨hVodd, hcop⟩ := pairConfinement_p_actor_coprime p hp hpodd V R hV hRodd hRcop
  have hlocal := local_point_datum_at_class_fixed_point h.local_datum hsclass gamma hgamma
  have hcentral : Subgroup.centralizer ({s} : Set G) ≤ J := point_centralizer_le hlocal
  have hVR : V ≤ Subgroup.normalizer (R : Set G) :=
    hVD.trans (Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p D))
  have hYescape := pairConfinement_odd_inverted_centralizer_escape J V R s hsorder
    hcentral hVgamma hVodd hsV hVR hsR hcop hescape
  rw [pairConfinement_closure_inverted_set P z s hsinvert] at hYescape
  apply hYescape
  exact (inf_le_inf_right _ (pairConfinement_theta_le p D)).trans
    (pairConfinement_intersection_centralizer_fixed h P X hXH hXM hcomm s
      hsclass hsA hsX gamma hgamma)

end CFSG.ShultStronglyClosedTI
