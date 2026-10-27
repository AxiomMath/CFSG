module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementInversion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

universe u

variable {G : Type u} [Group G]

theorem pairConfinement_closure_pair_intersections
    (H P : Subgroup G) (z : G) (hz : orderOf z = 2) (hPH : P ≤ H)
    (n : G) (hn : n ∈ minimalLocalFailureInvertedOvergroup P z) :
    let V := minimalLocalFailurePairConfinementClosure P z
    let s := rightConjugateElem z n
    V ≤ H ⊓ rightConjugate H n ∧ V ≤ H ⊓ rightConjugate H s ∧
      s ∈ Subgroup.normalizer (V : Set G) := by
  let V := minimalLocalFailurePairConfinementClosure P z
  let A := minimalLocalFailureInvertedOvergroup P z
  have hVH : V ≤ H := (pairConfinement_closure_le P z).trans hPH
  have hzA : z ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hsA : rightConjugateElem z n ∈ A :=
    A.mul_mem (A.mul_mem (A.inv_mem hn) hzA) hn
  have hnV := pairConfinement_closure_normalizer P z hz hn
  have hsV := pairConfinement_closure_normalizer P z hz hsA
  exact ⟨le_inf hVH (normalized_subgroup_le_right_conjugate_overgroup V H n hVH hnV),
    le_inf hVH (normalized_subgroup_le_right_conjugate_overgroup V H _ hVH hsV), hsV⟩

theorem pairConfinement_rebased_pair (H : Subgroup G) (n : G) :
    pairPointStabilizer (rightConjugate H n)
      (rightCosetMk (rightConjugate H n) n⁻¹) = H ⊓ rightConjugate H n := by
  unfold pairPointStabilizer
  rw [rebaseRightCoset_stabilizer H n, rebaseRightCoset_stabilizer H n,
    rebaseRightCoset_mk, rebaseRightCoset_mk, mul_one, mul_inv_cancel,
    rightCosetStabilizer_base, rightCosetStabilizer_mk, inf_comm]

theorem pairConfinement_rebased_triple (H : Subgroup G) (n s : G) :
    triplePointStabilizer (rightConjugate H n) s
      (rightCosetMk (rightConjugate H n) n⁻¹) =
        (H ⊓ rightConjugate H s) ⊓ (H ⊓ rightConjugate H n) := by
  unfold triplePointStabilizer
  rw [pairConfinement_rebased_pair, rebaseRightCoset_stabilizer H n,
    rebaseRightCoset_translate, rebaseRightCoset_mk, mul_inv_cancel,
    rightCosetTranslate_mk, one_mul, rightCosetStabilizer_mk]
  ext a
  simp only [Subgroup.mem_inf]
  tauto

variable [Finite G]

theorem pairConfinement_restricted_flip_intersection
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (N : Subgroup G) (hzN : z ∈ N) (hescape : ¬ N ≤ H)
    (n : G) (hnN : n ∈ N) (hnH : n ∉ H) :
    ∃ r ∈ conjugacyWithin N z, r ∉ H ∧
      H ⊓ rightConjugate H r = H ⊓ rightConjugate H n := by
  let nN : N := ⟨n, hnN⟩
  let beta := rightCosetMk (H.subgroupOf N) nN
  have hbeta : beta ≠ rightCosetMk (H.subgroupOf N) 1 := by
    intro heq
    have hh := congrArg (subgroupRightCosetInclusion H N) heq
    change rightCosetMk H n = rightCosetMk H 1 at hh
    have hrel := Quotient.exact hh
    change (QuotientGroup.rightRel H) n 1 at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    exact hnH (H.inv_mem_iff.mp (by simpa only [one_mul] using hrel))
  have hlocal := (involution_point_subgroup_inheritance h N hzN hescape).1
  obtain ⟨r, hr⟩ := original_pair_flip_exists hlocal beta hbeta
  have hrambient := subgroup_flip_mem_ambient hzN hr
  have hcoset : rightCosetMk H (r : G) = rightCosetMk H n := by
    have hh := hrambient.2
    simpa only [rightCosetTranslate_mk, one_mul, beta, subgroupRightCosetInclusion_mk,
      nN] using hh
  have hrclass : (r : G) ∈ conjugacyWithin N z := by
    obtain ⟨a, ha⟩ := hr.1
    exact ⟨a, congrArg Subtype.val ha⟩
  refine ⟨r, hrclass, ?_, ?_⟩
  · intro hrH
    have hbase : rightCosetMk H (r : G) = rightCosetMk H 1 := by
      simpa only [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul]
        using (point_right_base_fixed_iff H (r : G)).mpr hrH
    have hrel := Quotient.exact (hcoset.symm.trans hbase)
    change (QuotientGroup.rightRel H) n 1 at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    exact hnH (H.inv_mem_iff.mp (by simpa only [one_mul] using hrel))
  · have heq := congrArg (rightCosetStabilizer H) hcoset
    rw [rightCosetStabilizer_mk, rightCosetStabilizer_mk] at heq
    rw [heq]

end CFSG.ShultStronglyClosedTI
