module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalPointHullClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCountingInheritance
public import CFSG.StronglyEmbedded.BenderBorelTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def InvolutionPointCentralSylow (z : G) : Prop :=
  ∃ (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G)),
    (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)

structure MinimalInvolutionPointLocalFailure [Finite G] (H : Subgroup G) (z : G) : Prop where
  local_datum : InvolutionPointLocalEmbedding H z
  central_sylow : InvolutionPointCentralSylow z
  failure : ¬ fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z))
  smaller : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
    ∀ (A : Subgroup Y) (a : Y), InvolutionPointLocalEmbedding A a →
      InvolutionPointCentralSylow a →
        fusionStronglyEmbedded (A.subgroupOf (involutionPointHull a))

theorem minimalLocalFailure_hull_eq_normalClosure (z : G) :
    involutionPointHull z = Subgroup.normalClosure ({z} : Set G) := by
  have hclass : Group.conjugatesOfSet ({z} : Set G) = conjugatesOf z := by
    ext x
    rw [Group.mem_conjugatesOfSet_iff]
    change (∃ a, a ∈ ({z} : Set G) ∧ IsConj a x) ↔ IsConj z x
    simp only [Set.mem_singleton_iff, exists_eq_left]
  change Subgroup.closure (involutionPointClass z) =
    Subgroup.closure (Group.conjugatesOfSet ({z} : Set G))
  rw [hclass, localPointHullClass_eq_conjugatesOf]

theorem minimalLocalFailure_hull_normal (z : G) : (involutionPointHull z).Normal := by
  rw [minimalLocalFailure_hull_eq_normalClosure]
  infer_instance

theorem minimalLocalFailure_internal_hull_top [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    involutionPointHull zL = (⊤ : Subgroup L) := by
  change Subgroup.closure (involutionPointClass _) = ⊤
  rw [localPointHullClass_eq_conjugatesOf]
  exact localPointHull_internal_class_generates h

theorem minimalLocalFailure_hull_not_le_point [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : ¬ involutionPointHull z ≤ H := by
  intro hLH
  apply h.proper
  apply top_unique
  intro g _
  have hg : g ∈ (H : Set G) * (involutionPointHull z : Set G) := by
    rw [← localPointHull_group_eq_point_mul h]
    trivial
  obtain ⟨a, ha, l, hl, rfl⟩ := Set.mem_mul.mp hg
  exact H.mul_mem ha (hLH hl)

theorem minimalLocalFailure_hull_eq_top [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) : involutionPointHull z = ⊤ := by
  by_contra hproper
  let L := involutionPointHull z
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  obtain ⟨hlocal, hcentral⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow.involution_point_subgroup_inheritance
      h.local_datum L zL.property (minimalLocalFailure_hull_not_le_point h.local_datum)
  have hcard : Nat.card L < Nat.card G := by
    simpa only [Subgroup.card_top] using
      Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hstrong := h.smaller L hcard (H.subgroupOf L) zL hlocal
    (hcentral h.central_sylow)
  rw [minimalLocalFailure_internal_hull_top h.local_datum] at hstrong
  have himage : ((H.subgroupOf L).subgroupOf (⊤ : Subgroup L)).map
      Subgroup.topEquiv.toMonoidHom = H.subgroupOf L := by
    change ((H.subgroupOf L).subgroupOf (⊤ : Subgroup L)).map
      (⊤ : Subgroup L).subtype = H.subgroupOf L
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  have htransport := hstrong.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L)
  rw [himage] at htransport
  exact h.failure htransport

theorem minimalLocalFailure_no_central_involution [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) :
    ∀ c ∈ Subgroup.center G, orderOf c ≠ 2 := by
  intro c hc horder
  have hcentralizer : Subgroup.centralizer ({c} : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hc)
  have hescape : ¬ Subgroup.centralizer ({c} : Set G) ≤ H := by
    rw [hcentralizer]
    exact fun hle => h.local_datum.proper (top_le_iff.mp hle)
  have hcomm : Commute c z :=
    (Subgroup.mem_center_iff.mp hc z).symm
  have hhull : localInvolutionPointHull z c = involutionPointHull z := by
    rw [localInvolutionPointHull, hcentralizer, Subgroup.coe_top, Set.inter_univ]
    rfl
  have hlocal := h.local_datum.local_embedding c horder hcomm hescape
  rw [hhull] at hlocal
  exact h.failure hlocal

theorem minimalLocalFailure_normal_two_subgroup_central [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q) : Q ≤ Subgroup.center G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hzS, hcenter⟩ := h.central_sylow
  have hQS : Q ≤ (S : Subgroup G) := hQ.le_sylow_of_normal S
  let C := Subgroup.centralizer (Q : Set G)
  have hzC : z ∈ C := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    have hcomm := Subgroup.mem_center_iff.mp hcenter (⟨q, hQS hq⟩ : (S : Subgroup G))
    exact congrArg Subtype.val hcomm
  have hclass : involutionPointClass z ⊆ C := by
    rintro x ⟨g, rfl⟩
    exact (inferInstance : C.Normal).conj_mem' z hzC g
  have htop : (⊤ : Subgroup G) ≤ C := by
    rw [← minimalLocalFailure_hull_eq_top h]
    exact (Subgroup.closure_le _).mpr hclass
  exact Subgroup.centralizer_eq_top_iff_subset.mp (top_le_iff.mp htop)

theorem minimalLocalFailure_two_core_eq_bot [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) : CFSG.pCore 2 G = ⊥ := by
  have hcentral := minimalLocalFailure_normal_two_subgroup_central h (CFSG.pCore 2 G)
    CFSG.pCore_isPGroup
  by_contra hne
  have hcard : Nat.card (CFSG.pCore 2 G) ≠ 1 := fun hc => hne (Subgroup.card_eq_one.mp hc)
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    exact hcard (by simpa only [hnzero, pow_zero] using hn)
  have hdiv : 2 ∣ Nat.card (CFSG.pCore 2 G) := by
    rw [hn]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.pCore 2 G) 2 hdiv
  exact minimalLocalFailure_no_central_involution h c (hcentral c.property)
    ((Subgroup.orderOf_coe c).trans hc)

end CFSG.ShultStronglyClosedTI
