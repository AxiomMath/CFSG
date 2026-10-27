module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Criteria

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

omit [Finite G] in
theorem ggStdSubIOne_iff_le_of_stdSubPre (hDJ : LargeEvenStdSubPre p B x L D J) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ↔ Bs ⊓ Subgroup.centralizer (J : Set G) ≤ B := by
  refine ⟨fun h => h.trans hDJ.1, fun h g hg => ?_⟩
  rw [hDJ.2.2.2.2.2.2]
  exact ⟨h hg, hg.2⟩

omit [Finite G] in
theorem ggStdSubIOne_of_eq (hDJ : LargeEvenStdSubPre p B x L D J) :
    B ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
  hDJ.2.2.2.2.2.2.ge

theorem ggStdSubIOne_of_card_le (hDJ : LargeEvenStdSubPre p B x L D J) (hBBs : B ≤ Bs)
    (hcard : Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 2) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  have hle : D ≤ Bs ⊓ Subgroup.centralizer (J : Set G) := by
    rw [hDJ.2.2.2.2.2.2]
    exact inf_le_inf_right _ hBBs
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hDJ.2.2.1]; exact hcard)
  exact heq.ge

end Criteria

@[expose] def GGStdSubIOneExistInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L → GGBstar p B Bs →
      ∃ D J : Subgroup G, LargeEvenStdSub p B x L D J ∧
        Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

@[expose] def GGStdSubIOneProperInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L → GGBstar p B Bs → B ≠ Bs →
      ∃ D J : Subgroup G, LargeEvenStdSub p B x L D J ∧
        Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

@[expose] def GGStdSubIOneRootInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L → GGBstar p B Bs → B ≠ Bs →
      ∃ D J : Subgroup G, LargeEvenStdSub p B x L D J ∧
        ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧ B ≤ Subgroup.normalizer (T : Set G)

theorem ggStdSubIOneProperInput_of_root (h : GGStdSubIOneRootInput) : GGStdSubIOneProperInput := by
  intro G _ _ p B Bs x L hI hBs hne
  obtain ⟨D, J, hDJ, hT⟩ := h G p B Bs x L hI hBs hne
  exact ⟨D, J, hDJ, ggStdSubBstarCentralizer_of_twoSubgroup ⟨hI, hBs, hDJ⟩ hT⟩

theorem ggStdSubIOneExistInput_of_proper (hb : GGStdSubPreInput) (hP : GGStdSubIOneProperInput) :
    GGStdSubIOneExistInput := by
  intro G _ _ p B Bs x L hI hBs
  by_cases hB : B = Bs
  · subst hB
    obtain ⟨D, J, hDJ⟩ := exists_stdSub_of_stdSubPre (hb G p B x L hI)
    exact ⟨D, J, hDJ, ggStdSubIOne_of_eq hDJ.1⟩
  · exact hP G p B Bs x L hI hBs hB

theorem ggStdSubPreInput_of_iOne (ha : GGBstarInput) (h : GGStdSubIOneExistInput) :
    GGStdSubPreInput := by
  intro G _ _ p B x L hI
  obtain ⟨Bs, hBs⟩ := ha G p B x L hI
  obtain ⟨D, J, hDJ, -⟩ := h G p B Bs x L hI hBs
  exact ⟨D, J, hDJ.1⟩

section Genuine

theorem ggSecOneFiveV2I1Input_of_inputs_mk (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput)
    (hb : GGStdSubIOneExistInput) (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input)
    (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput)
    (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput)
    (hg₂ : GGOmegaOneInput) (hR : GGInnerDiagMarkingInput) : GGSecOneFiveV2I1Input := by
  intro G _ _ _ hnonab hK hchar he4 p hp B x L hS hst
  have hI : GGThmIHyp p B x L := ⟨inferInstance, hnonab, hK, hchar, he4, hp, hS, hst⟩
  obtain ⟨Bs, hBs⟩ := ha G p B x L hI
  obtain ⟨D, J, hDJ, hI1⟩ := hb G p B Bs x L hI hBs
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hInn := hc₂ G p B Bs x L D J hcfg hOp
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  obtain ⟨t, n, f, ψ, hpres⟩ := he G p B Bs x L D J hcfg hOp hInn hNoTr hW
  have hnc := ha₀ G p B x L hI
  have hBsN := bstar_le_normalizer_ggG0 hS hnc hDJ.1 hBs
  have hVI := hf G p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN
  have hNBs := hg₁ G p B Bs x L D J hcfg hOp hInn hNoTr
    (ggInnerDiagOn_of_presents_mk hR hpres hBsN hVI)
  have hCB := centralizer_le_normalizer_ggG0 hS hnc hDJ.1
  have hNB := normalizer_le_of_frattini hp.1 hBs (hg₂ G p B Bs x L D J hcfg hOp hInn) hCB hNBs
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  exact ⟨Bs, D, J, ⟨t, n, f, ψ, hBs, hDJ, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩,
    ⟨hBsN, hVI⟩, hNB, hNBs⟩, hI1⟩

theorem ggSecOneFiveV2I1Input_of_inputs (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput)
    (hb : GGStdSubIOneExistInput) (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input)
    (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput)
    (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput)
    (hg₂ : GGOmegaOneInput) (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput) :
    GGSecOneFiveV2I1Input := by
  intro G _ _ _ hnonab hK hchar he4 p hp B x L hS hst
  have hI : GGThmIHyp p B x L := ⟨inferInstance, hnonab, hK, hchar, he4, hp, hS, hst⟩
  obtain ⟨Bs, hBs⟩ := ha G p B x L hI
  obtain ⟨D, J, hDJ, hI1⟩ := hb G p B Bs x L hI hBs
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hInn := hc₂ G p B Bs x L D J hcfg hOp
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  obtain ⟨t, n, f, ψ, hpres⟩ := he G p B Bs x L D J hcfg hOp hInn hNoTr hW
  have hnc := ha₀ G p B x L hI
  have hBsN := bstar_le_normalizer_ggG0 hS hnc hDJ.1 hBs
  have hVI := hf G p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN
  have hNBs := hg₁ G p B Bs x L D J hcfg hOp hInn hNoTr
    (ggInnerDiagOn_of_presents hR1 hR hpres hBsN hVI)
  have hCB := centralizer_le_normalizer_ggG0 hS hnc hDJ.1
  have hNB := normalizer_le_of_frattini hp.1 hBs (hg₂ G p B Bs x L D J hcfg hOp hInn) hCB hNBs
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  exact ⟨Bs, D, J, ⟨t, n, f, ψ, hBs, hDJ, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩,
    ⟨hBsN, hVI⟩, hNB, hNBs⟩, hI1⟩

end Genuine

theorem ggSecOneFiveI1Input_of_inputs (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput)
    (hb : GGStdSubIOneExistInput) (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input)
    (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput)
    (he : GGPropFiveTwentyOneInput) (hf : GGHypSixInput) (hg₁ : GGCorFiveTwentyInput)
    (hg₂ : GGOmegaOneInput) (ha' : GGBstarRankInput) : GGSecOneFiveI1Input := by
  intro G _ _ _ hnonab hK hchar he4 p hp B x L hS hst
  have hI : GGThmIHyp p B x L := ⟨inferInstance, hnonab, hK, hchar, he4, hp, hS, hst⟩
  obtain ⟨Bs, hBs⟩ := ha G p B x L hI
  obtain ⟨D, J, hDJ, hI1⟩ := hb G p B Bs x L hI hBs
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hInn := hc₂ G p B Bs x L D J hcfg hOp
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  have hMark := he G p B Bs x L D J hcfg hOp hInn hNoTr hW
  have hnc := ha₀ G p B x L hI
  have hBsN := bstar_le_normalizer_ggG0 hS hnc hDJ.1 hBs
  have hVI := hf G p B Bs x L D J hcfg hOp hInn hMark hBsN
  have hMarkVI : GGInnerDiagOn Bs (ggG0 p B x L D J) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨hBsN, h⟩) hVI
  have hNBs := hg₁ G p B Bs x L D J hcfg hOp hInn hNoTr hMarkVI
  have hCB := centralizer_le_normalizer_ggG0 hS hnc hDJ.1
  have hNB := normalizer_le_of_frattini hp.1 hBs (hg₂ G p B Bs x L D J hcfg hOp hInn) hCB hNBs
  have hpre : GGSixHypPre p B Bs x L D J := ⟨hBs, hDJ, hMarkVI, hNB, hNBs⟩
  have hrank := ha' G p B Bs x L D J hI hpre
  exact ⟨Bs, D, J, ⟨⟨hBs.1, hBs.2.1, hrank⟩, hDJ, hMarkVI, hNB, hNBs⟩, hI1⟩

end CFSG.StandardType
