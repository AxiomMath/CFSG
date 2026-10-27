module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineProducer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeFrameShared
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pjf_indep_to_datumA {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {n : ℕ} (h : GGResXDatumAIndep p Bs X n) : GGResXDatumA p Bs X n := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem ggTwoNodeKFixLineFrameInput_of_shared (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hDim : GGTwoNodeRowDimKnown)
    (hX : GGResXDichotomyInput) : GGTwoNodeKFixLineFrameInput := by
  intro G _ _ p _ B Bs x L D J y K N hH hF hS hE hrow hp2 hN5 hN10 hpN hXI hx
  have hLd : GGResXDatum p Bs L := by
    refine (hX G p B Bs x L D J y K hH).1.resolve_right ?_
    intro hseven
    obtain ⟨labJ, labX, hΛJ, hΛX, hLabJ, hLabX, hp7, h5⟩ := hseven
    obtain ⟨hcfg, -, -, -, hnb, -, -⟩ := hH
    exact ggSeven_L_absurd hTCJ hRig hcfg hp7 hnb hΛX hLabX h5
  obtain ⟨V, iV1, iV2, ι, h, α, r, T, iT, s, hdim, hpair, hr, hclosure, hs, hconn, -, hfixs, hx0,
    hxnot, hnt, hind⟩ := ggTwoNodeFrame_of_datums hFix hWA hDim hH hrow hp2 hN5 hpN
      (pjf_indep_to_datumA hXI) hLd hx
  exact ⟨V, iV1, iV2, ι, h, α, r, T, iT, s, hdim, hind hXI, hpair, hr, hclosure, hs, hconn, hfixs,
    hx0, hxnot, hnt⟩

theorem ggTwoNodeKFixLineInput_of_zs_shared (hZS : ZS.UseInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hDim : GGTwoNodeRowDimKnown) (hX : GGResXDichotomyInput) : GGTwoNodeKFixLineInput :=
  ggTwoNodeKFixLineInput_of_zs_frame hZS
    (ggTwoNodeKFixLineFrameInput_of_shared hTCJ hRig hFix hWA hDim hX)

end CFSG.StandardType

end
