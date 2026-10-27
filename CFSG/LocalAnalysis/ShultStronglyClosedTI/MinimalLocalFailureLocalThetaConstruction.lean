module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaCoreJoin
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.OrderReductions.PrimePart
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem class_closure_join_eq_zpowers_join (A T U : Subgroup G) (z : G)
    (hclass : conjugacyWithin A z = conjugacyWithin T z) (hTU : T ≤ U) :
    Subgroup.closure (conjugacyWithin A z) ⊔ U = Subgroup.zpowers z ⊔ U := by
  apply le_antisymm
  · refine sup_le ((Subgroup.closure_le _).mpr ?_) le_sup_right
    rw [hclass]
    rintro a ⟨t, rfl⟩
    let P := Subgroup.zpowers z ⊔ U
    have htP : (t : G) ∈ P := (le_sup_right : U ≤ P) (hTU t.property)
    have hzP : z ∈ P := (le_sup_left : Subgroup.zpowers z ≤ P)
      (Subgroup.mem_zpowers z)
    exact P.mul_mem (P.mul_mem (P.inv_mem htP) hzP) htP
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) le_sup_right
    exact (le_sup_left : Subgroup.closure (conjugacyWithin A z) ≤
      Subgroup.closure (conjugacyWithin A z) ⊔ U)
      (Subgroup.subset_closure (show z ∈ conjugacyWithin A z from ⟨1, by simp⟩))

theorem local_theta_auxiliary_construction [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (beta : numeratorRightOrbit H Y (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) :
    let B := pairPointStabilizer H beta.val
    let J := pairOddCore H beta.val
    let D := Y ⊓ B
    let T := Y ⊓ J
    let Theta := minimalLocalFailurePairConfinementTheta p D
    let U := T ⊔ Theta
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    D ≤ H ⊓ Y ∧ T ≤ D ∧ (T.subgroupOf D).Normal ∧
      U ≤ D ∧ (U.subgroupOf D).Normal ∧ Odd (Nat.card U) ∧
      primePart p (Nat.card U) = primePart p (Nat.card T) ∧
      (∀ Q : Sylow p T, ∃ R : Sylow p U,
        (R : Subgroup U).map U.subtype = (Q : Subgroup T).map T.subtype) ∧
      I ≤ H ⊓ Y ∧ (I.subgroupOf (H ⊓ Y)).Normal ∧ z ∈ I ∧
      K ≤ H ⊓ Y ∧ D ≤ Subgroup.normalizer (K : Set G) ∧
      (I.subgroupOf K).Normal ∧ K = Subgroup.zpowers z ⊔ U ∧
      (U : Set G) = (T : Set G) * (Theta : Set G) ∧
      (K : Set G) = (I : Set G) * (U : Set G) := by
  let B := pairPointStabilizer H beta.val
  let J := pairOddCore H beta.val
  let D := Y ⊓ B
  let T := Y ⊓ J
  let Theta := minimalLocalFailurePairConfinementTheta p D
  let U := T ⊔ Theta
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  have hJB : J ≤ B := Subgroup.map_subtype_le _
  have hJnormal : (J.subgroupOf B).Normal := by
    have heq : J.subgroupOf B = CFSG.oddCore B := by
      exact Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    rw [heq]
    infer_instance
  let : (J.subgroupOf B).Normal := hJnormal
  have hDpoint : D ≤ H ⊓ Y :=
    le_inf (inf_le_right.trans (pairPointStabilizer_le_point H beta.val)) inf_le_left
  have hTD : T ≤ D := inf_le_inf_left Y hJB
  have hTnormalizer : D ≤ Subgroup.normalizer (T : Set G) := by
    exact (le_inf (inf_le_left.trans Y.le_normalizer)
      (inf_le_right.trans (Subgroup.le_normalizer_of_normal_subgroupOf hJB))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTnormal : (T.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTD).mpr hTnormalizer
  have hTodd : Odd (Nat.card T) := (pairOddCore_odd H beta.val).of_dvd_nat
    (Subgroup.card_dvd_of_le (inf_le_right : T ≤ J))
  obtain ⟨hUD, hUnormal, hUodd, hpart, hSylow⟩ :=
    canonical_theta_join_properties hp D T hTD hTnormal hTodd
  have hzpoint : z ∈ H ⊓ Y := ⟨h.distinguished_mem, hzY⟩
  have hIpoint : I ≤ H ⊓ Y :=
    minimalLocalFailurePairActionPointHull_le_point (H ⊓ Y) hzpoint
  have hInormal : (I.subgroupOf (H ⊓ Y)).Normal :=
    minimalLocalFailurePairActionPointHull_normal_in_point (H ⊓ Y) hzpoint
  let : (I.subgroupOf (H ⊓ Y)).Normal := hInormal
  have hInorm : H ⊓ Y ≤ Subgroup.normalizer (I : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hIpoint
  have hzI : z ∈ I := Subgroup.subset_closure ⟨1, by simp⟩
  have hKpoint : K ≤ H ⊓ Y := sup_le hIpoint (hUD.trans hDpoint)
  let : (U.subgroupOf D).Normal := hUnormal
  have hKnormalizer : D ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf (hDpoint.trans hInorm)
      (Subgroup.le_normalizer_of_normal_subgroupOf hUD)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup I U)
  have hIKnormal : (I.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (hKpoint.trans hInorm)
  have hclass := localNormalizer_point_class_eq_pair_odd_core_class h S hzS hzcenter
    Y hzY hescape beta hbeta
  have hgen : K = Subgroup.zpowers z ⊔ U :=
    class_closure_join_eq_zpowers_join (H ⊓ Y) T U z hclass le_sup_left
  have hUproduct : (U : Set G) = (T : Set G) * (Theta : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left T Theta
      ((pairConfinement_theta_le p D).trans hTnormalizer)
  have hKproduct : (K : Set G) = (I : Set G) * (U : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left I U ((hUD.trans hDpoint).trans hInorm)
  exact ⟨hDpoint, hTD, hTnormal, hUD, hUnormal, hUodd, hpart, hSylow,
    hIpoint, hInormal, hzI, hKpoint, hKnormalizer, hIKnormal, hgen, hUproduct, hKproduct⟩

end CFSG.ShultStronglyClosedTI.LocalTheta
