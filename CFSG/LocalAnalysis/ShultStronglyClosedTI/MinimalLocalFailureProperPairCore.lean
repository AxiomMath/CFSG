module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOddCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailureProperPairOddCore (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) : Subgroup G :=
  (oddCore (minimalLocalFailureProperPairHull H z beta t)).map
    (minimalLocalFailureProperPairHull H z beta t).subtype

theorem minimalLocalFailureProperPairOddCore_subgroupOf (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    (minimalLocalFailureProperPairOddCore H z beta t).subgroupOf
      (minimalLocalFailureProperPairHull H z beta t) =
      oddCore (minimalLocalFailureProperPairHull H z beta t) := by
  exact Subgroup.comap_map_eq_self_of_injective
    (minimalLocalFailureProperPairHull H z beta t).subtype_injective _

theorem minimalLocalFailureProperPairOddCore_normal_in_hull (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    ((minimalLocalFailureProperPairOddCore H z beta t).subgroupOf
      (minimalLocalFailureProperPairHull H z beta t)).Normal := by
  rw [minimalLocalFailureProperPairOddCore_subgroupOf]
  infer_instance

theorem minimalLocalFailureProperPairOddCore_le_hull (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    minimalLocalFailureProperPairOddCore H z beta t ≤
      minimalLocalFailureProperPairHull H z beta t := Subgroup.map_subtype_le _

theorem minimalLocalFailureProperPairOddCore_odd [Finite G] (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    Odd (Nat.card (minimalLocalFailureProperPairOddCore H z beta t)) := by
  rw [minimalLocalFailureProperPairOddCore, Subgroup.card_subtype]
  exact CFSG.ComponentClassification.OddCore.odd_card _

private theorem closure_pair_eq_zpowers_sup (z s : G) :
    Subgroup.closure ({z, s} : Set G) = Subgroup.zpowers z ⊔ Subgroup.zpowers s := by
  have hpair : ({z, s} : Set G) = {z} ∪ {s} := by
    ext x
    simp [or_comm]
  rw [hpair, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem minimalLocalFailure_commuting_class_member [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    ∃ s ∈ conjugacyWithin H z, s ≠ z ∧ Commute z s := by
  by_contra hnone
  have hisolated : ∀ g : G, Commute (g⁻¹ * z * g) z → g⁻¹ * z * g = z := by
    intro g hcomm
    have hconjH : g⁻¹ * z * g ∈ H :=
      point_centralizer_le h.local_datum
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq)
    have hgH : g ∈ H := (pointClass_conjugate_mem_iff h.local_datum g).mp hconjH
    by_contra hne
    exact hnone ⟨g⁻¹ * z * g, ⟨⟨g, hgH⟩, rfl⟩, hne, hcomm.symm⟩
  obtain ⟨_, hfactor⟩ := native_zStar_of_isolated_involution
    h.local_datum.distinguished_order hisolated
  apply h.local_datum.proper
  apply top_unique
  intro g _
  obtain ⟨c, hc, x, hx, hcx⟩ := hfactor g
  have hxone : x = 1 := by
    apply Subgroup.mem_bot.mp
    simpa only [minimalLocalFailure_odd_core_eq_bot h] using hx
  rw [hxone, mul_one] at hcx
  rw [hcx]
  exact point_centralizer_le h.local_datum hc

theorem minimalLocalFailureProperPair_four_group [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    ∃ s ∈ conjugacyWithin H z, s ≠ z ∧ Commute z s ∧
      IsElemAbelian 2 (Subgroup.closure ({z, s} : Set G)) ∧
      Nat.card (Subgroup.closure ({z, s} : Set G)) = 4 ∧
      Subgroup.closure ({z, s} : Set G) ≤
        H ⊓ minimalLocalFailureProperPairHull H z beta t := by
  obtain ⟨s, hsclass, hsne, hscomm⟩ := minimalLocalFailure_commuting_class_member h
  have hsambient : s ∈ involutionPointClass z := by
    obtain ⟨a, ha⟩ := hsclass
    exact ⟨a, ha⟩
  have hsorder : orderOf s = 2 :=
    order_two_of_mem_pointClass h.local_datum.distinguished_order hsambient
  obtain ⟨hV, hcard, _⟩ :=
    CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group
      h.local_datum.distinguished_order hsorder hscomm hsne
  have hclass := minimalLocalFailureProperPair_class_subset
    h.local_datum h.central_sylow hbeta ht
  have hzclass : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
  refine ⟨s, hsclass, hsne, hscomm, ?_, ?_, ?_⟩
  · rwa [closure_pair_eq_zpowers_sup]
  · rwa [closure_pair_eq_zpowers_sup]
  · rw [closure_pair_eq_zpowers_sup]
    exact sup_le (Subgroup.zpowers_le.mpr (hclass hzclass))
      (Subgroup.zpowers_le.mpr (hclass hsclass))

theorem minimalLocalFailureProperPairOddCore_le_point [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    minimalLocalFailureProperPairOddCore H z beta t ≤ H := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  obtain ⟨s, hsclass, hsne, hscomm⟩ := minimalLocalFailure_commuting_class_member h
  have hclass := minimalLocalFailureProperPair_class_subset
    h.local_datum h.central_sylow hbeta ht
  let zK : K := ⟨z, minimalLocalFailureProperPair_distinguished_mem H z beta t⟩
  let sK : K := ⟨s, (hclass hsclass).2⟩
  have hzorder : orderOf zK = 2 :=
    (Subgroup.orderOf_coe zK).symm.trans h.local_datum.distinguished_order
  have hsambient : s ∈ involutionPointClass z := by
    obtain ⟨a, ha⟩ := hsclass
    exact ⟨a, ha⟩
  have hsorder : orderOf sK = 2 := (Subgroup.orderOf_coe sK).symm.trans
    (order_two_of_mem_pointClass h.local_datum.distinguished_order hsambient)
  have hcomm : Commute zK sK := Subtype.ext hscomm.eq
  have hne : sK ≠ zK := fun heq => hsne (congrArg Subtype.val heq)
  obtain ⟨hV, hcard, _⟩ :=
    CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group
      hzorder hsorder hcomm hne
  have hzM : zK ∈ M := h.local_datum.distinguished_mem
  have hsM : sK ∈ M := (hclass hsclass).1
  have hVM : Subgroup.zpowers zK ⊔ Subgroup.zpowers sK ≤ M :=
    sup_le (Subgroup.zpowers_le.mpr hzM) (Subgroup.zpowers_le.mpr hsM)
  have hNM : oddCore K ≤ M := oddCore_le_stronglyEmbedded_of_elementary
    M (Subgroup.zpowers zK ⊔ Subgroup.zpowers sK)
    (minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper)
    hVM hV (by omega)
  intro n hn
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
  exact hNM ha

theorem minimalLocalFailureProperPairOddCore_le_pair_stabilizer [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    minimalLocalFailureProperPairOddCore H z beta t ≤ pairPointStabilizer H beta := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let tK : K := ⟨t, minimalLocalFailureProperPair_flip_mem H z beta t⟩
  have hNH := minimalLocalFailureProperPairOddCore_le_point h hbeta ht hproper
  have hbetaeq : beta = rightCosetMk H t := by
    simpa only [rightCosetTranslate_mk, one_mul] using ht.2.symm
  have hstabilizer : rightCosetStabilizer H beta = rightConjugate H t := by
    rw [hbetaeq, rightCosetStabilizer_mk]
  intro n hn
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
  refine ⟨?_, ?_⟩
  · rw [rightCosetStabilizer_base]
    exact hNH (Subgroup.mem_map_of_mem K.subtype ha)
  · change (a : G) ∈ rightCosetStabilizer H beta
    rw [hstabilizer]
    have hconjN : t * (a : G) * t⁻¹ ∈ minimalLocalFailureProperPairOddCore H z beta t :=
      Subgroup.mem_map_of_mem K.subtype
        ((inferInstance : (oddCore K).Normal).conj_mem a ha tK)
    have hconjH : t * (a : G) * t⁻¹ ∈ H := hNH hconjN
    have hright := rightConjugateElem_mem_rightConjugate (g := t) hconjH
    simpa only [rightConjugateElem, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hright

end CFSG.ShultStronglyClosedTI
