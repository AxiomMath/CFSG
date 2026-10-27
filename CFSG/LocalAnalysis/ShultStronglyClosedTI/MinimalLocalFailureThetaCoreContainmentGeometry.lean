module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorEquivariant

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ThetaCoreContainment

open CFSG.Open
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe u

variable {G : Type u} [Group G]

theorem original_pair_class_eq [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    conjugacyWithin H z = conjugacyWithin (pairPointStabilizer H beta) z := by
  have hfactor := point_subgroup_eq_centralizer_mul_inverted_set
    h S hzS hzcenter hbeta ht
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    have ha : (a : G) ∈ (H : Set G) := a.property
    rw [hfactor] at ha
    obtain ⟨c, hc, i, hi, hci⟩ := Set.mem_mul.mp ha
    have hiB := (pairOddCore_le H beta t).1 hi.1
    refine ⟨⟨i, hiB⟩, ?_⟩
    have hcconj : c⁻¹ * z * c = z := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    rw [← hci, mul_inv_rev]
    calc
      i⁻¹ * z * i = i⁻¹ * (c⁻¹ * z * c) * i := by rw [hcconj]
      _ = (i⁻¹ * c⁻¹) * z * (c * i) := by group
  · rintro ⟨b, hb⟩
    exact ⟨⟨b, pairPointStabilizer_le_point H beta b.property⟩, hb⟩

theorem pair_element_transports_triple (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (b : G) (hb : b ∈ pairPointStabilizer H beta) :
    rightConjugate (triplePointStabilizer H z beta) b =
      triplePointStabilizer H (rightConjugateElem z b) beta := by
  have hB : rightConjugate (pairPointStabilizer H beta) b =
      pairPointStabilizer H beta :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((pairPointStabilizer H beta).inv_mem hb))
  have hbeta := (mem_rightCosetStabilizer_iff H beta b).mp hb.2
  have hgamma : rightCosetTranslate H (rightCosetTranslate H beta z) b =
      rightCosetTranslate H beta (rightConjugateElem z b) := by
    calc
      rightCosetTranslate H (rightCosetTranslate H beta z) b =
          rightCosetTranslate H beta (z * b) := rightCosetTranslate_mul H beta z b
      _ = rightCosetTranslate H beta (b * rightConjugateElem z b) := by
        simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]
      _ = rightCosetTranslate H (rightCosetTranslate H beta b)
          (rightConjugateElem z b) := (rightCosetTranslate_mul H beta b _).symm
      _ = rightCosetTranslate H beta (rightConjugateElem z b) := by rw [hbeta]
  change ((pairPointStabilizer H beta) ⊓
    rightCosetStabilizer H (rightCosetTranslate H beta z)).map
      (MulAut.conj b⁻¹).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj b⁻¹).injective]
  change rightConjugate (pairPointStabilizer H beta) b ⊓
    rightConjugate (rightCosetStabilizer H (rightCosetTranslate H beta z)) b = _
  rw [hB, rightCosetStabilizer_right_translate, hgamma]
  rfl

theorem pair_element_transports_triple_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (b : G) (hb : b ∈ pairPointStabilizer H beta) :
    rightConjugate ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype) b =
        pairOddCore H beta ⊓ triplePointStabilizer H (rightConjugateElem z b) beta := by
  have hJ : rightConjugate (pairOddCore H beta) b = pairOddCore H beta := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact (generatedPairGrowth_normalizer_le_characteristic_image
      (pairPointStabilizer H beta) (CFSG.oddCore (pairPointStabilizer H beta))
      (CFSG.ComponentClassification.OddCore.characteristic _))
        (Subgroup.le_normalizer ((pairPointStabilizer H beta).inv_mem hb))
  rw [triple_odd_core_eq_pair_intersection h S hzS hzcenter beta hbeta]
  change (pairOddCore H beta ⊓ triplePointStabilizer H z beta).map
    (MulAut.conj b⁻¹).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj b⁻¹).injective]
  change rightConjugate (pairOddCore H beta) b ⊓
    rightConjugate (triplePointStabilizer H z beta) b = _
  rw [hJ, pair_element_transports_triple H z beta b hb]

end CFSG.ShultStronglyClosedTI.ThetaCoreContainment
