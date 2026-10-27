module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthInvariantSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthKernelTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaNormalization

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.OrderReductions.PrimePart
open CFSG.ShultStronglyClosedTI.LocalTheta
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem exists_full_sylow_and_normalized_orderZJ
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hne : ∃ X A v, Admissible H z beta p X A v) :
    ∃ Q : Sylow p (pairOddCore H beta), ∃ v : G,
      v ∈ rightPairFlipFiber H z beta ∧
      v ∈ Subgroup.normalizer
        ((Q : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype : Set G) ∧
      (Q : Subgroup (pairOddCore H beta)) ≠ ⊥ ∧
      z ∈ Subgroup.normalizer
        ((orderZJ ((Q : Subgroup (pairOddCore H beta)).map
          (pairOddCore H beta).subtype)).map
            ((Q : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype).subtype :
              Set G) ∧
      (orderZJ ((Q : Subgroup (pairOddCore H beta)).map
        (pairOddCore H beta).subtype)).map
          ((Q : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype).subtype ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, A, v, hadm, hmax⟩ := exists_maximal_admissible H z beta p hne
  let Y := Subgroup.normalizer (X : Set G)
  let T := Y ⊓ pairOddCore H beta
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hadm.distinguished_invariant
  have hescape : ¬ Y ≤ H := by
    intro hYH
    have hvH : v ∈ H := hYH hadm.flip_normalizes
    have hbase : rightCosetTranslate H (rightCosetMk H 1) v = rightCosetMk H 1 := by
      rw [← pointRightCosetMul_eq_translate]
      exact (point_right_base_fixed_iff H v).mpr hvH
    exact hbeta (hadm.flip.2.symm.trans hbase)
  have hbetaOrbit : beta ∈ numeratorRightOrbit H Y (rightCosetMk H 1) := by
    refine ⟨v, hadm.flip_normalizes, ?_⟩
    rw [pointRightCosetMul_eq_translate]
    exact hadm.flip.2
  let betaY : numeratorRightOrbit H Y (rightCosetMk H 1) := ⟨beta, hbetaOrbit⟩
  obtain ⟨Q, hAQ, hvQ, hQne⟩ := admissible_invariant_sylow_containing_witness
    h.local_datum beta hbeta p hp X A v hadm
  let D := Y ⊓ pairPointStabilizer H beta
  let Theta := minimalLocalFailurePairConfinementTheta p D
  let U := T ⊔ Theta
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  obtain ⟨S2, hzS2, hzcenter⟩ := h.central_sylow
  obtain ⟨_hDpoint, _hTD, _hTnormal, _hUD, _hUnormal, _hUodd, _hpart, _hSylowU,
    _hIpoint, _hInormal, hzI, _hKpoint, _hKnorm, _hIKnormal, _hgen, _hUprod, _hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S2 hzS2 hzcenter Y hzY hescape
      betaY hbeta hp
  obtain ⟨_hsol, hfour, _htwo, hclass, _himage⟩ :=
    local_theta_actual_structure h hcomm X hadm.subgroup_le_point hadm.subgroup_ne_bot
      hadm.distinguished_invariant hescape hadm.hull_rank betaY hbeta hp
  obtain ⟨hWodd, _hThetaW, hWconfined, _hpartK, hSylowK⟩ :=
    local_theta_actual_capture h hcomm X hadm.subgroup_le_point hadm.subgroup_ne_bot
      hadm.distinguished_invariant hescape hadm.hull_rank betaY hbeta hp hpodd
      A hadm.witness_le hadm.witness_prime hadm.witness_distinguished_invariant
        hadm.witness_noncentral
  have hnorm := local_theta_actual_normalization h hcomm X hadm.subgroup_le_point
    hadm.subgroup_ne_bot hadm.distinguished_invariant hescape hadm.hull_rank betaY hbeta
    hp hpodd A hadm.witness_le hadm.witness_prime hadm.witness_distinguished_invariant
      hadm.witness_noncentral
  have hTK : T ≤ K := (le_sup_left : T ≤ U).trans le_sup_right
  have hzK : z ∈ K := (le_sup_left : I ≤ K) hzI
  have hrankK : 2 ≤ twoRank K := numeric_rank_two_of_four hfour
  have hWE : (CFSG.pPrimeCore p K).map K.subtype ≤ triplePointStabilizer H z beta :=
    hWconfined.trans (inf_le_right.trans inf_le_left)
  obtain ⟨S, hSQ⟩ := hSylowK Q
  have hprod := (hnorm Q).1
  obtain ⟨w, _hw, hadm1, hQ1J, hR1Q1, hR1char, hQ1p, hv1Q1, hR1ZJ, hQ1ne, hQ1card⟩ :=
    kernel_transfer_orderZJ_admissible h.local_datum beta p hp hpodd X A v hadm Q hAQ
      hvQ hQne K hTK hzK hrankK hclass hWodd hWE S hSQ hprod
  let QG := (Q : Subgroup T).map T.subtype
  let R := (orderZJ QG).map QG.subtype
  let Q1 := rightConjugate QG w⁻¹
  let R1 := rightConjugate R w⁻¹
  let A1 := rightConjugate A w⁻¹
  let v1 := rightConjugateElem v w⁻¹
  have hbound : primePart p (Nat.card
      (Subgroup.normalizer (R1 : Set G) ⊓ pairOddCore H beta : Subgroup G)) ≤
        Nat.card Q1 := (hmax R1 A1 v1 hadm1).trans_eq hQ1card.symm
  obtain ⟨P, hP⟩ := full_sylow_of_characteristic_prime_part_bound p hp
    (pairOddCore H beta) R1 Q1 hQ1J hR1Q1 hR1char hQ1p hbound
  have hPne : (P : Subgroup (pairOddCore H beta)) ≠ ⊥ := by
    intro hbot
    apply hQ1ne
    change Q1 = ⊥
    rw [← hP, hbot, Subgroup.map_bot]
  refine ⟨P, v1, hadm1.flip, ?_, hPne, ?_, ?_⟩
  · rw [hP]
    exact hv1Q1
  · rw [hP, ← hR1ZJ]
    exact invariant_subgroup_mem_normalizer hadm1.distinguished_invariant
  · rw [hP, ← hR1ZJ]
    exact hadm1.subgroup_ne_bot

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
