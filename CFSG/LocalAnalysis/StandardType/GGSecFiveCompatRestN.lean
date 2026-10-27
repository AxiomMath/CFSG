module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Inputs

theorem ggSecFiveCompatRestN1Input_of_n (h : GGSecFiveCompatRestNInput) :
    GGSecFiveCompatRestN1Input :=
  fun G _ _ p B Bs x L D J hcfg hOp hInn hNT hs hall hd t n f ψ hpres hL =>
    h G p B Bs x L D J hcfg hOp hInn hNT (fun hW => hs hW.1) hd t n f ψ hpres hL

theorem ggSecFiveCompatRestA11Input_of_n (h : GGSecFiveCompatRestNInput) :
    GGSecFiveCompatRestA11Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hA hd t n f ψ hpres hL
  obtain ⟨-, -, y, K, hK, -, hn⟩ := hA
  exact h G p B Bs x L D J hcfg hOp hInn hNT (fun hW => hn (hW.2 y K hK)) hd t n f ψ hpres hL

theorem ggSecFiveCompatRestWInput'_of_rest (h : GGSecFiveCompatRestInput) :
    GGSecFiveCompatRestWInput' :=
  fun G _ _ p B Bs x L D J hcfg hOp hInn hNT _ hd t n f ψ hpres hL =>
    h G p B Bs x L D J hcfg hOp hInn hNT hd t n f ψ hpres hL

theorem ggSecFiveCompatRestA11Input_of_rest (h : GGSecFiveCompatRestInput) :
    GGSecFiveCompatRestA11Input :=
  fun G _ _ p B Bs x L D J hcfg hOp hInn hNT _ hd t n f ψ hpres hL =>
    h G p B Bs x L D J hcfg hOp hInn hNT hd t n f ψ hpres hL

theorem ggSecFiveCompatRestWInput_of_w' (h : GGSecFiveCompatRestWInput') :
    GGSecFiveCompatRestWInput :=
  fun G _ _ p B Bs x L D J hcfg hOp hInn hNT hw hd t n f ψ hpres hL =>
    h G p B Bs x L D J hcfg hOp hInn hNT hw.2 hd t n f ψ hpres hL

theorem ggSecFiveCompatRestN1Input_of_w' (h : GGSecFiveCompatRestWInput') :
    GGSecFiveCompatRestN1Input :=
  fun G _ _ p B Bs x L D J hcfg hOp hInn hNT _ hall hd t n f ψ hpres hL =>
    h G p B Bs x L D J hcfg hOp hInn hNT hall hd t n f ψ hpres hL

theorem ggSecFiveCompatRestWInput'_iff :
    GGSecFiveCompatRestWInput' ↔ GGSecFiveCompatRestWInput ∧ GGSecFiveCompatRestN1Input := by
  refine ⟨fun h => ⟨ggSecFiveCompatRestWInput_of_w' h, ggSecFiveCompatRestN1Input_of_w' h⟩,
    fun ⟨hW, hN1⟩ G _ _ p B Bs x L D J hcfg hOp hInn hNT hall hd t n f ψ hpres hL => ?_⟩
  by_cases hs : GGScalarsPmOne Bs
  · exact hW G p B Bs x L D J hcfg hOp hInn hNT ⟨hs, hall⟩ hd t n f ψ hpres hL
  · exact hN1 G p B Bs x L D J hcfg hOp hInn hNT hs hall hd t n f ψ hpres hL

theorem ggSecFiveCompatRestNInput_of_known
    (h : GGSecFiveNonWeylKnown) (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hN1 : GGSecFiveCompatRestN1Input) (hA11 : GGSecFiveCompatRestA11Input) :
    GGSecFiveCompatRestNInput := by
  obtain ⟨hnc, hR, hW, hC, hTCJ, hTP, hCoord, -⟩ := h
  have hZ := ggNbrBstarCenterInput_of_centerPCyclic hC
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hnw hd t n f ψ hpres hL
  by_cases hall : GGSecFiveWeylCase' p B Bs x D J
  · exact hN1 G p B Bs x L D J hcfg hOp hInn hNT (fun hs => hnw ⟨hs, hall⟩) hall hd t n f ψ
      hpres hL
  · unfold GGSecFiveWeylCase' at hall
    push Not at hall
    obtain ⟨y, K, hK, hnr⟩ := hall
    have hRest : GGSecFiveRestHyp p B Bs x L D J :=
      ⟨hcfg, hOp, hInn, hNT, hd, fun ⟨n, f, hs⟩ => hL hs.leviCase⟩
    exact hA11 G p B Bs x L D J hcfg hOp hInn hNT
      (ggSecFiveA11Config_of_nonReflGen hRig hTCJ hTP hCoord hRest hK
        (ggNbr_exc_of_not_reflGen (ggNbrReflGenNonSplitFull_of_rank hnc hR hW hRig hZ) hTB hRig hZ
          hraw hiso hRest hK hnr) hnr) hd t n f ψ hpres hL

theorem ggSecFiveCompatRestInput_of_known
    (h : GGSecFiveNonWeylKnown) (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hW : GGSecFiveCompatRestWInput') (hA11 : GGSecFiveCompatRestA11Input) :
    GGSecFiveCompatRestInput :=
  ggSecFiveCompatRestInput_of_split (ggSecFiveCompatRestWInput_of_w' hW)
    (ggSecFiveCompatRestNInput_of_known h hRig hTB hraw hiso (ggSecFiveCompatRestN1Input_of_w' hW)
      hA11)

theorem ggSecFiveCompatRestInput_iff_known
    (h : GGSecFiveNonWeylKnown) (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGSecFiveCompatRestInput ↔ GGSecFiveCompatRestWInput' ∧ GGSecFiveCompatRestA11Input :=
  ⟨fun hC => ⟨ggSecFiveCompatRestWInput'_of_rest hC, ggSecFiveCompatRestA11Input_of_rest hC⟩,
    fun ⟨hW, hA⟩ => ggSecFiveCompatRestInput_of_known h hRig hTB hraw hiso hW hA⟩

end Inputs

end CFSG.StandardType

end
