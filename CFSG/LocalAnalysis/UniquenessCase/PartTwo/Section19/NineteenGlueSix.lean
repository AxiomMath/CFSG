module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nineteen_glue_six (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    R19_glue_6At D V₀ V p L A t B r A₀ H h := by
  change ∃ K : Subgroup G, K ≤ H ∧ CFSG.IsComponent (K.subgroupOf H) ∧
    ActsFaithfullyOn V₀ K
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hV0p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV0el
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
  let Vh : Subgroup ↥H := V₀.subgroupOf H
  have hO2 : CFSG.pCore 2 ↥H = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥H)
      (f := H.subtype) H.subtype_injective).mp
    simpa [CFSG.Open.pCoreOf] using h.hO2
  have hVhp : IsPGroup 2 Vh := hV0p.comap_subtype
  have hVhne : Vh ≠ ⊥ := by
    intro hbot
    apply hV0ne
    have hmap := congrArg (Subgroup.map H.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hV0H, Subgroup.map_bot] at hmap
  have hTIH : CFSG.CGT.Timmesfeld75.IsTI Vh :=
    CFSG.CGT.Timmesfeld75.IsTI.subgroupOf hTI H
  have hC : ∀ v ∈ Vh, v ≠ 1 →
      Subgroup.centralizer ({v} : Set ↥H) ≤ Subgroup.normalizer (Vh : Set ↥H) := by
    intro v hv hv1
    exact CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTIH hv hv1
  have h24_1 : ⁅V₀, Oodd H⁆ = ⊥ := nineteen_twentyfour_one D h
  have hO : CFSG.pPrimeCore 2 ↥H ≤ Subgroup.centralizer (Vh : Set ↥H) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.commutator_comm]
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr ?_
    intro v hv o ho
    have hv0 : (v : G) ∈ V₀ := hv
    have ho0 : (o : G) ∈ Oodd H := Subgroup.mem_map_of_mem H.subtype ho
    have hG : ⁅(v : G), (o : G)⁆ = 1 := by
      have hmem : ⁅(v : G), (o : G)⁆ ∈ (⊥ : Subgroup G) :=
        Subgroup.commutator_le.mp (le_of_eq h24_1) (v : G) hv0 (o : G) ho0
      exact Subgroup.mem_bot.mp hmem
    have hmap : ((⁅v, o⁆ : ↥H) : G) = 1 := by
      change H.subtype ⁅v, o⁆ = 1
      rw [map_commutatorElement]
      exact hG
    exact Subtype.ext hmap
  obtain ⟨K, hKcomp, hfaith⟩ :=
    CFSG.GroupTheory.exists_isComponent_inf_centralizer_eq_bot hO2 hVhp hVhne hC hO
  let KG : Subgroup G := K.map H.subtype
  have hKGH : KG ≤ H := Subgroup.map_subtype_le K
  have hKGsub : KG.subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  have hKGcomp : CFSG.IsComponent (KG.subgroupOf H) := by
    rw [hKGsub]
    exact hKcomp
  refine ⟨KG, hKGH, hKGcomp, ?_⟩
  change V₀ ⊓ Subgroup.centralizer (KG : Set G) = ⊥
  rw [eq_bot_iff]
  intro x hx
  have hxV0 : x ∈ V₀ := hx.1
  have hxC : x ∈ Subgroup.centralizer (KG : Set G) := hx.2
  have hxH : x ∈ H := hV0H hxV0
  let xh : ↥H := ⟨x, hxH⟩
  have hxhV : xh ∈ Vh := Subgroup.mem_subgroupOf.mpr hxV0
  have hxhC : xh ∈ Subgroup.centralizer (K : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply Subtype.ext
    have hkG : (k : G) ∈ KG := Subgroup.mem_map_of_mem H.subtype hk
    simpa using Subgroup.mem_centralizer_iff.mp hxC (k : G) hkG
  have hmem : xh ∈ Vh ⊓ Subgroup.centralizer (K : Set ↥H) := ⟨hxhV, hxhC⟩
  rw [hfaith] at hmem
  have hx1 : xh = 1 := Subgroup.mem_bot.mp hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)

theorem nineteen_glue_six_closed (D : Data G) : R19_glue_6 D :=
  fun V₀ V p L A t B r A₀ H h => nineteen_glue_six D h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
