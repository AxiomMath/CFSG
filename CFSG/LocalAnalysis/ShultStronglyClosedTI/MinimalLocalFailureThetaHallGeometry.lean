module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaHallAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNormalIntersection
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalTheta

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ThetaHall

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_pair_and_flip_normalize_theta
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) (p : ℕ) (hp : p.Prime) :
    Subgroup.closure ((pairPointStabilizer H beta : Set G) ∪ {t}) ≤
      Subgroup.normalizer
        (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) : Set G) := by
  let B := pairPointStabilizer H beta
  let J := pairOddCore H beta
  let C := minimalLocalFailurePairConfinementTheta p B
  have hBC : B ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p B)
  have htC : t ∈ Subgroup.normalizer (C : Set G) := by
    have htJ := generatedPairGrowth_flip_normalizes_pair_odd_core h hbeta ht
    have htheta : C = (CFSG.pPrimeCore p J).map J.subtype :=
      generatedPairGrowth_ambient_canonical_core_eq B hp
    rw [htheta]
    exact generatedPairGrowth_normalizer_le_characteristic_image J
      (CFSG.pPrimeCore p J) inferInstance htJ
  apply (Subgroup.closure_le _).mpr
  exact Set.union_subset hBC (Set.singleton_subset_iff.mpr htC)

theorem original_deficient_theta_sylow_geometry
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime)
    (hcontain : minimalLocalFailurePairConfinementTheta p (triplePointStabilizer H z beta) ≤
      minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta))
    (hindex : q ∣ (minimalLocalFailurePairConfinementTheta p
        (triplePointStabilizer H z beta)).relIndex
      (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)))
    (Q : Sylow q (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
      triplePointStabilizer H z beta : Subgroup G))
    (hzQ : z ∈ Subgroup.normalizer
      (((Q : Subgroup _).map
        (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
          triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hQne : ((Q : Subgroup _).map
      (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
        triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥) :
    let QG := (Q : Subgroup _).map
      (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
        triplePointStabilizer H z beta).subtype
    let Y := Subgroup.normalizer (QG : Set G)
    Y ≠ ⊤ ∧ ¬ Y ≤ H ∧
      beta ∈ numeratorRightOrbit H Y (rightCosetMk H 1) ∧
      2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin Y z)) := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let C := minimalLocalFailurePairConfinementTheta p B
  let D := C ⊓ E
  let QG := (Q : Subgroup D).map D.subtype
  let Y := Subgroup.normalizer (QG : Set G)
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hintersection : C ⊓ E = minimalLocalFailurePairConfinementTheta p E :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.properHull_theta_inf_subgroup_eq
      p hp B E inf_le_left hcontain
  have hindexD : q ∣ D.relIndex C := by
    dsimp only [D]
    rw [hintersection]
    exact hindex
  have hqm : q ∣ Nat.card (conjugacyWithin H z) :=
    hindex.trans (original_theta_intersection_relIndex_dvd_class h.local_datum
      S hzS hzcenter beta hbeta t ht p hp hcontain)
  have hdeficient := sylow_deficient_of_relIndex_prime q hq C E hindexD Q
  obtain ⟨hYproper, hescape, ⟨y, hy⟩, hrank, _hlocal, _hflip⟩ :=
    minimalLocalFailureNormalIntersectionSylowHullRank h hcomm beta hbeta t ht C
      (pairConfinement_theta_le p B)
      (original_pair_and_flip_normalize_theta h.local_datum beta hbeta t ht p hp)
      q hq hqm Q hzQ hQne hdeficient
  exact ⟨hYproper, hescape, ⟨y, y.property, hy⟩, hrank⟩

theorem original_deficient_theta_sylow_capture
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) (p q : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hq : q.Prime)
    (hcontain : minimalLocalFailurePairConfinementTheta p (triplePointStabilizer H z beta) ≤
      minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta))
    (hindex : q ∣ (minimalLocalFailurePairConfinementTheta p
        (triplePointStabilizer H z beta)).relIndex
      (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)))
    (Q : Sylow q (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
      triplePointStabilizer H z beta : Subgroup G))
    (hzQ : z ∈ Subgroup.normalizer
      (((Q : Subgroup _).map
        (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
          triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hQne : ((Q : Subgroup _).map
      (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
        triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥)
    (A : Subgroup G) (hAJ : A ≤ pairOddCore H beta) (hAp : IsPGroup p A)
    (hAz : rightConjugate A z = A)
    (hAnoncentral : ¬ A ≤ Subgroup.centralizer ({z} : Set G))
    (hAQ : A ≤ Subgroup.normalizer
      (((Q : Subgroup _).map
        (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
          triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    minimalLocalFailurePairConfinementTheta p
      (Subgroup.normalizer
        (((Q : Subgroup _).map
          (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ⊓
            triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) ⊓
        pairPointStabilizer H beta) ≤ triplePointStabilizer H z beta := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let C := minimalLocalFailurePairConfinementTheta p B
  let D := C ⊓ E
  let QG := (Q : Subgroup D).map D.subtype
  let Y := Subgroup.normalizer (QG : Set G)
  obtain ⟨_hproper, hescape, hbetaOrbit, hrank⟩ :=
    original_deficient_theta_sylow_geometry h hcomm beta hbeta t ht p q hp hq
      hcontain hindex Q hzQ hQne
  have hQH : QG ≤ H := (Subgroup.map_subtype_le _).trans
    (inf_le_left.trans ((pairConfinement_theta_le p B).trans
      (pairPointStabilizer_le_point H beta)))
  have hQz : rightConjugate QG z = QG := rightConjugate_eq_self_of_mem_normalizer hzQ
  let betaY : numeratorRightOrbit H Y (rightCosetMk H 1) := ⟨beta, hbetaOrbit⟩
  have hAnoncomm : ⁅A, Subgroup.zpowers z⁆ ≠ ⊥ := by
    intro hzero
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
    apply hAnoncentral
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (((Subgroup.mem_centralizer_iff.mp (hcent ha)) z (Subgroup.mem_zpowers z)).symm)
  have hcapture := minimalLocalFailure_local_theta_and_ZJ_normalizer h hcomm
    QG hQH hQne hQz hescape hrank betaY hbeta hp hpodd
      ⟨A, le_inf hAQ hAJ, hAp, hAz, hAnoncomm⟩
  exact hcapture.1

end CFSG.ShultStronglyClosedTI.ThetaHall
