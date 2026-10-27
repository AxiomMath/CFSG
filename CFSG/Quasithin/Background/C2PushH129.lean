module

public import CFSG.Quasithin.Background.C2PushA3
public import CFSG.Quasithin.Background.C2PushMain
public import CFSG.Quasithin.Background.C129Used
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.Quasithin.EmptyFaithful.S14113bMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C2Push

variable {G : Type} [Group G] [Finite G]

theorem le_or_isShort2_of_asc129_used (h129 : ASC129StatementUsed G) {M R H L : Subgroup G}
    (hMc : CharTwo M) (hMs : IsSQTKIn M) (hR : IsTwoRadicalIn M R) (hcgs : cgsIn M R ≤ H)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : IsSylowTwoOf (R ⊓ L) L) : L ≤ H ∨ IsShort2 L := by
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hRM : R ≤ M := hR.1
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : Y ≤ M := conjClosure_sup_le hRM hLM
  have hRY : R ≤ Y := le_sup_right
  have hRH : R ≤ H := fun x hx =>
    hcgs (inf_normalizer_le_cgsIn hR.2.1 ⟨hRM hx, Subgroup.le_normalizer hx⟩)
  have hYsyl : IsSylowTwoOf R Y := isSylowTwoOf_conjClosure_sup hR hL hLq hsyl
  have hYc : CharTwo Y := charTwo_of_pCoreOf_le hMc ((c2_1_pCore_le hR).trans hRY) hYM
  have hYs : IsSQTKIn Y := hMs.mono hYM
  have hcgsY : cgsIn Y R ≤ Y ⊓ H :=
    le_inf (cgsIn_le Y R) ((C2Nine.cgsIn_mono_left hYM R).trans hcgs)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 Y R (Y ⊓ H) hYs hYc hYsyl hcgsY inf_le_left
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  · right
    obtain ⟨i, hi⟩ := hq
    have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
      ((hLb i).1.1.1.2.2.2.1).resolve_right hi
    exact isShort2_of_isBlock2_conjClosure_sup hR hL hLq (hLb i).1.1 hBq
  · left
    push Not at hq
    exact le_of_isBlock2_card_three hL hLq hRM hYsyl hRH Lb
      (fun i => ⟨(hLb i).1.1, hq i⟩) hprod

theorem le_of_mem_cComp_of_hypC23_h129_used {T Mc M H R : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hyp : HypC23 M R H)
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (h129 : ASC129StatementUsed G) {L : Subgroup G}
    (hL : L ∈ cComp M) (hLc : CharTwo L)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : L ≤ H := by
  by_cases hRN : R ≤ Subgroup.normalizer (L : Set G)
  · exact le_of_le_normalizer_of_hypC23 h hM hyp hL hLc hLq hRN
  · have hsyl : IsSylowTwoOf (R ⊓ L) L :=
      isSylowTwoOf_inf_of_not_le_normalizer hyp.radical
        (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hM.2) hTR hL hLq hRN
    rcases le_or_isShort2_of_asc129_used h129 (charTwo_of_inM h hM) hyp.sqtk hyp.radical hyp.cgs hL hLq
      hsyl with hle | hshort
    · exact hle
    · exact absurd (isFaithfulLocal_of_isShort2 h hM hL hshort) (h.faithful_empty L)

theorem layer_le_imageOTwoQuot_h129_used {T Mc M H R : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hyp : HypC23 M R H) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (h129 : ASC129StatementUsed G) : CFSG.layer (OTwoQuot M) ≤ imageOTwoQuot M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharM : CharTwo M := charTwo_of_inM h hM
  have hsolv : Group.IsSolvable (CFSG.Open.pCore 2 ↥M) := isSolvable_pCore_two M
  simp only [CFSG.layer.eq_sSup]
  refine sSup_le fun K hK => ?_
  have hKc : K ∈ cComp (⊤ : Subgroup (OTwoQuot M)) := mem_cComp_top_of_isComponent hK
  obtain ⟨L', hL', hLK⟩ := (cComp_quotient_bijOn (CFSG.Open.pCore 2 ↥M) hsolv).surjOn hKc
  subst hLK
  have hL : L'.map M.subtype ∈ cComp M := map_subtype_mem_cComp hL'
  have hLc : CharTwo (L'.map M.subtype) :=
    charTwo_of_isSubnormal_of_charTwo hcharM (subnormal_of_mem_cComp hL)
  have hLq := isQuasisimple_pCore_quotient rfl hK.1 (subnormal_of_mem_cComp hL)
  have hLH : L'.map M.subtype ≤ H :=
    le_of_mem_cComp_of_hypC23_h129_used h hM hyp hTR h129 hL hLc hLq
  have hle : L' ≤ H.subgroupOf M := fun x hx => hLH ⟨x, hx, rfl⟩
  exact Subgroup.map_mono hle

theorem oTwoEIn_le_of_hypC23_h129_used {T Mc M H R : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hyp : HypC23 M R H) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (h129 : ASC129StatementUsed G) (hOH : pCoreOf 2 M ≤ H) : oTwoEIn M ≤ H := by
  have hlayer := layer_le_imageOTwoQuot_h129_used h hM hyp hTR h129
  rw [oTwoEIn_eq_map_O2E]
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (QuotientGroup.mk z : OTwoQuot M) ∈ CFSG.layer (OTwoQuot M) := hz
  exact mem_of_mk_mem_imageOTwoQuot hOH (hlayer hz')

theorem stageLemma14113_of_inputs_h129_used (h110 : StageLemma14110)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hTail : Stage14113CaseTwo) : StageLemma14113 := by
  intro G _ _ T Mc h M H hM hTH hHM hR hC
  have hyp : HypC23 M (pCoreOf 2 H) H := hypC23_of_cgs h hM hHM hR hC
  have hOH : pCoreOf 2 M ≤ H := (c2_1_pCore_le hyp.radical).trans (pCoreOf_le 2 H)
  have hTR : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hTH.trans (le_normalizer_pCoreOf 2 H)
  have hRT : pCoreOf 2 H ≤ T := by
    obtain ⟨S, hS⟩ := h.exists_sylow
    have := pCoreOf_two_le_sylow H S (hS ▸ hTH)
    rwa [hS] at this
  have hlayer : CFSG.layer (OTwoQuot M) ≤ imageOTwoQuot M H :=
    layer_le_imageOTwoQuot_h129_used h hM hyp hTR (h129 G)
  by_cases hF : oTwoFIn M ≤ H
  ·
    left
    have hgen : CFSG.generalizedFitting (OTwoQuot M) ≤ imageOTwoQuot M H :=
      sup_le (fitting_le_imageOTwoQuot hF) hlayer
    have hFs : oTwoFstarIn M ≤ H := by
      rw [← map_O2Fstar_eq_oTwoFstarIn]
      rintro _ ⟨z, hz, rfl⟩
      exact mem_of_mk_mem_imageOTwoQuot hOH (hgen hz)
    refine ⟨hFs, ?_⟩
    have := a4_4_1 (pCoreOf_le_oTwoFstarIn M) (le_inf (oTwoFstarIn_le M) hFs)
      (a44Hyp_oTwoFstarIn M)
    rwa [inf_eq_right.mpr hHM] at this
  ·
    right
    have hFchar : CharTwo (oTwoFIn M) :=
      CFSG.Quasithin.CT.CharTwo.of_normal (charTwo_of_inM h hM) C2Six.oTwoFIn_le
        C2Six.normal_oTwoFIn_subgroupOf
    obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two_thompson_solv hyp hFchar
    have hr : 0 < r := by
      by_contra hr0
      have hr0' : r = 0 := Nat.eq_zero_of_not_pos hr0
      subst hr0'
      apply hF
      intro x hx
      obtain ⟨m, hm, y, -, hxy⟩ := hprod x hx
      have hxm : x = m := by simpa using hxy
      rw [hxm]
      exact hm.1
    obtain ⟨hblock, hA3, -, hJ⟩ := hLb ⟨0, hr⟩
    obtain ⟨hMc, hZ⟩ := h110 G T Mc h M (Lb ⟨0, hr⟩) (pCoreOf 2 H) hM (isBlock2_of_oTwoFIn hblock)
      hA3 (c2_1_pCore_le hyp.radical) hRT hJ
    have hE : oTwoEIn M ≤ H := oTwoEIn_le_of_hypC23_h129_used h hM hyp hTR (h129 G) hOH
    have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ H :=
      hTail G T Mc h M H hM hTH hHM hR hC hE hMc hZ r Lb hLb hprod hF
    refine ⟨hZ, hMc, ⟨hM.1, hHM⟩, fun M₂ hM₂ => ?_⟩
    exact (h.mc_unique M₂ hM₂.1 (hCZ.trans hM₂.2)).trans hMc.symm

theorem stageLemma14113_of_stages_h129_used (h110 : StageLemma14110)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G) : StageLemma14113 :=
  stageLemma14113_of_inputs_h129_used h110 h129 stage14113CaseTwo

end CFSG.Quasithin
