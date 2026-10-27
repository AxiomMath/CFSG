module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeRel
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

namespace AmbientH

variable {V H T : Subgroup G}

theorem normalizer_eq {A : Subgroup G} (hAH : A ≤ H) :
    Subgroup.normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (Subgroup.normalizer (A : Set G)).subgroupOf H := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      have h1 := (h ⟨g, hAH hg⟩).1 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 h1
    · intro hg
      have hgH : g ∈ H := by
        have h1 : (x : G) * g * (x : G)⁻¹ ∈ H := hAH hg
        have h2 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
        rw [h2]
        exact H.mul_mem (H.mul_mem (H.inv_mem x.2) h1) x.2
      have h2 := (h ⟨g, hgH⟩).2 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 h2
  · intro h g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h g

theorem two_lt_card (hVH : V ≤ H) (h : 2 < Nat.card V) : 2 < Nat.card ↥(V.subgroupOf H) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
  exact h

theorem isCalH (h : IsCalH V H) : IsCalH (V.subgroupOf H) (⊤ : Subgroup ↥H) := by
  obtain ⟨hVH, hchar, hodd⟩ := h
  refine ⟨le_top, ?_, ?_⟩
  · change (⊤ : Subgroup ↥H) ⊓
        Subgroup.centralizer ((pCoreOf 2 (⊤ : Subgroup ↥H) : Subgroup ↥H) : Set ↥H) ≤
        pCoreOf 2 (⊤ : Subgroup ↥H)
    rw [pCoreOf_top_eq_subgroupOf]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨-, hxC⟩ := hx
    rw [Subgroup.mem_subgroupOf]
    refine hchar (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzH : z ∈ H := CFSG.openPCoreOf_le 2 H hz
    have hzmem : (⟨z, hzH⟩ : ↥H) ∈ (pCoreOf 2 H).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hz
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC (⟨z, hzH⟩ : ↥H) hzmem
    exact congrArg Subtype.val hcomm
  · have hnorm : (⊤ : Subgroup ↥H) ⊓
        Subgroup.normalizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H) =
        (Subgroup.normalizer (V : Set G)).subgroupOf H := by
      rw [top_inf_eq, normalizer_eq hVH]
    rw [hnorm, Subgroup.relIndex_top_right]
    change Odd ((Subgroup.normalizer (V : Set G)).relIndex H)
    rw [← Subgroup.inf_relIndex_left H (Subgroup.normalizer (V : Set G))]
    exact hodd

theorem not_isCalH0 (h : IsCalH V H) (h0 : ¬ IsCalH0 V H) :
    ¬ IsCalH0 (V.subgroupOf H) (⊤ : Subgroup ↥H) := by
  intro h'
  apply h0
  refine ⟨h, ?_⟩
  obtain ⟨-, hle⟩ := h'
  intro v hv
  have hvH : v ∈ H := h.1 hv
  have hv' : (⟨v, hvH⟩ : ↥H) ∈ V.subgroupOf H := Subgroup.mem_subgroupOf.mpr hv
  have hmem : (⟨v, hvH⟩ : ↥H) ∈ pCoreOf 2 (⊤ : Subgroup ↥H) := hle hv'
  rw [pCoreOf_top_eq_subgroupOf] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem isSylowIn (hVH : V ≤ H) (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    IsSylowIn 2 (T.subgroupOf H)
      ((⊤ : Subgroup ↥H) ⊓ Subgroup.normalizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H)) := by
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hnorm : (⊤ : Subgroup ↥H) ⊓
      Subgroup.normalizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (Subgroup.normalizer (V : Set G)).subgroupOf H := by
    rw [top_inf_eq, normalizer_eq hVH]
  refine ⟨?_, ?_, ?_⟩
  · rw [hnorm]
    intro t ht
    exact Subgroup.mem_subgroupOf.mpr (hT.le (Subgroup.mem_subgroupOf.mp ht)).2
  · exact hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  · rw [hnorm, ← Subgroup.inf_subgroupOf_left (Subgroup.normalizer (V : Set G)) H,
      Subgroup.relIndex_subgroupOf (inf_le_left : H ⊓ Subgroup.normalizer (V : Set G) ≤ H)]
    exact hT.not_dvd_relIndex

theorem hyp83 (h : Hyp83 V H T) :
    Hyp83 (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H) :=
  ⟨CFSG.Open.IsElemAbelian.comap h.elemAbelian H.subtype_injective,
    two_lt_card h.le_H h.two_lt_card, isTI_subgroupOf h.le_H h.isTI, isCalH h.isCalH,
    not_isCalH0 h.isCalH h.not_isCalH0, isSylowIn h.le_H h.sylow⟩

end AmbientH

end CFSG.LocalAnalysis.WeakClosure81

end
