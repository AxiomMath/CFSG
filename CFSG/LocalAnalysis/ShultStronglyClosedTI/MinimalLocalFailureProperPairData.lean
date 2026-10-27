module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairGeneratedHull
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailureProperPairHull (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) : Subgroup G :=
  Subgroup.closure (({z, t} : Set G) ∪
    (rightInvolutionCommutatorSubgroup t (pairOddCore H beta) : Set G))

theorem minimalLocalFailureProperPairHull_eq_native (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    minimalLocalFailureProperPairHull H z beta t = pairGeneratedHull H z beta t := by
  rw [minimalLocalFailureProperPairHull, Subgroup.closure_union,
    Subgroup.closure_eq]
  have hpair : ({z, t} : Set G) = {z} ∪ {t} := by
    ext x
    simp [or_comm]
  rw [hpair, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]
  rfl

theorem minimalLocalFailureProperPair_distinguished_mem (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    z ∈ minimalLocalFailureProperPairHull H z beta t := by
  apply Subgroup.subset_closure
  exact Or.inl (by simp)

theorem minimalLocalFailureProperPair_flip_mem (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) :
    t ∈ minimalLocalFailureProperPairHull H z beta t := by
  apply Subgroup.subset_closure
  exact Or.inl (by simp)

theorem minimalLocalFailureProperPair_not_le_point {H : Subgroup G} {z : G}
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    ¬ minimalLocalFailureProperPairHull H z beta t ≤ H := by
  intro hle
  exact pair_flip_not_mem_point hbeta ht
    (hle (minimalLocalFailureProperPair_flip_mem H z beta t))

theorem minimalLocalFailureProperPair_class_subset [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    conjugacyWithin H z ⊆ (H ⊓ minimalLocalFailureProperPairHull H z beta t : Set G) := by
  obtain ⟨S, hzS, hzcenter⟩ := hcentral
  have hclass := point_subgroup_class_le_pair_generated_hull h S hzS hzcenter hbeta ht
  rw [← minimalLocalFailureProperPairHull_eq_native] at hclass
  intro x hx
  refine ⟨?_, hclass hx⟩
  obtain ⟨a, rfl⟩ := hx
  exact H.mul_mem (H.mul_mem (H.inv_mem a.property) h.distinguished_mem) a.property

private theorem internal_hull_top_of_class_closure (K : Subgroup G) (z : G)
    (hzK : z ∈ K) (hgen : K = Subgroup.closure (conjugacyWithin K z)) :
    involutionPointHull (⟨z, hzK⟩ : K) = (⊤ : Subgroup K) := by
  let zK : K := ⟨z, hzK⟩
  have hclass : K.subtype '' involutionPointClass zK = conjugacyWithin K z := by
    ext x
    constructor
    · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹ * zK * g, ⟨g, rfl⟩, rfl⟩
  apply Subgroup.map_injective K.subtype_injective
  change (Subgroup.closure (involutionPointClass zK)).map K.subtype =
    (⊤ : Subgroup K).map K.subtype
  rw [K.subtype.map_closure, hclass, ← hgen, Subgroup.map_top, Subgroup.subtype_range]

theorem minimalLocalFailureProperPair_internal_hull_top [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    involutionPointHull (⟨z, minimalLocalFailureProperPair_distinguished_mem H z beta t⟩ :
      minimalLocalFailureProperPairHull H z beta t) = ⊤ := by
  obtain ⟨S, hzS, hzcenter⟩ := hcentral
  apply internal_hull_top_of_class_closure
  rw [minimalLocalFailureProperPairHull_eq_native]
  exact pair_generated_hull_eq_internal_class_closure h S hzS hzcenter hbeta ht

theorem minimalLocalFailureProperPair_stronglyEmbedded [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    fusionStronglyEmbedded (H.subgroupOf (minimalLocalFailureProperPairHull H z beta t)) := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let zK : K := ⟨z, minimalLocalFailureProperPair_distinguished_mem H z beta t⟩
  obtain ⟨hlocal, hcentral⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow.involution_point_subgroup_inheritance
      h.local_datum K zK.property (minimalLocalFailureProperPair_not_le_point hbeta ht)
  have hcard : Nat.card K < Nat.card G := by
    simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt hproper
  have hstrong := h.smaller K hcard (H.subgroupOf K) zK hlocal
    (hcentral h.central_sylow)
  have hhull : involutionPointHull zK = (⊤ : Subgroup K) :=
    minimalLocalFailureProperPair_internal_hull_top h.local_datum h.central_sylow hbeta ht
  rw [hhull] at hstrong
  have himage : ((H.subgroupOf K).subgroupOf (⊤ : Subgroup K)).map
      Subgroup.topEquiv.toMonoidHom = H.subgroupOf K := by
    change ((H.subgroupOf K).subgroupOf (⊤ : Subgroup K)).map
      (⊤ : Subgroup K).subtype = H.subgroupOf K
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  have htransport := hstrong.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K)
  rw [himage] at htransport
  exact htransport

end CFSG.ShultStronglyClosedTI
