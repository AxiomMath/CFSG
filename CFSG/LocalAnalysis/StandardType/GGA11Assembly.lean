module

public import CFSG.LocalAnalysis.StandardType.GGA11Rho
public import CFSG.LocalAnalysis.StandardType.GGA11Coherent
public import CFSG.LocalAnalysis.StandardType.GGA11Present
public import CFSG.LocalAnalysis.StandardType.GGA11StrongOfPresent
public import CFSG.LocalAnalysis.StandardType.GGA11GraphAut
public import CFSG.LocalAnalysis.StandardType.GGA11TorusModel
public import CFSG.LocalAnalysis.StandardType.GGA11GlueExt
public import CFSG.LocalAnalysis.StandardType.GGA11Coord
public import CFSG.LocalAnalysis.StandardType.GGA11LGen
public import CFSG.LocalAnalysis.StandardType.GGA11FrameAssemble
public import CFSG.LocalAnalysis.StandardType.GGA11NbrLine
public import CFSG.LocalAnalysis.StandardType.GGA11NbrInfty
public import CFSG.LocalAnalysis.StandardType.GGA11NbrFrob
public import CFSG.LocalAnalysis.StandardType.GGA11J9Gen
public import CFSG.LocalAnalysis.StandardType.GGA11L89B
public import CFSG.LocalAnalysis.StandardType.GGA11LemmaR
public import CFSG.LocalAnalysis.StandardType.GGA11BadFix
public import CFSG.LocalAnalysis.StandardType.GGA11NbrLabel
public import CFSG.LocalAnalysis.StandardType.GGA11NbrReflGen
public import CFSG.LocalAnalysis.StandardType.GGA11NbrBadA8
public import CFSG.LocalAnalysis.StandardType.GGA11NbrBadRefl
public import CFSG.LocalAnalysis.StandardType.GGA11AMat
public import CFSG.LocalAnalysis.StandardType.GGA11A8Homol
public import CFSG.LocalAnalysis.StandardType.GGA11ReflFix
public import CFSG.LocalAnalysis.StandardType.GGA11SylowSplit

public section

open CFSG CFSG.Assembly CFSG.StandardType

namespace CFSG.StandardType.A11

theorem ggSecFiveA11StrongInput_of_pieces
    (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeA11) (hTCJ : GGTCJKnown) (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hNS : GGNbrReflGenNonSplitInput)
    (h1 : A11FrameInput')
    (h3 : A11StrongOfDataInput) (h4 : A11NbrInput') : GGSecFiveA11StrongInput := by
  have h2a := CFSG.StandardType.A11.a11CoherentInput_holds
  have h2b := CFSG.StandardType.A11.a11RhoInput_holds
  intro G _ _ p B Bs x L D J hR hA
  obtain rfl : p = 7 := hA.1
  obtain ⟨y, K, φ₃, f, n, hcore, hext, hLcl⟩ := h1 hMp hLB G B Bs x L D J hR hA
  obtain ⟨hGlue, hrange, hnb, hBs, hx, hy, hD, hnL, hJK, hJ9⟩ := hcore
  have hFrame : A11FrameSpec B Bs x L D J y K φ₃ f n :=
    ⟨hGlue, hrange, hnb, hBs, hx, hy, hD, hnL, hJK, hJ9, hLcl⟩
  obtain ⟨Φ, hΦ⟩ := h2a G φ₃ f n hGlue
  obtain ⟨ρ, hρ⟩ := h2b G Φ hΦ.2.1 hΦ.2.2.2.2
  exact h3 G B Bs x L D J hR hA y K φ₃ f n Φ ρ hFrame hΦ hρ
    (h4 hTP hRig hTCJ hTB hNS hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ
      ⟨hR, hA, hFrame, hext, hΦ, hρ⟩)

theorem a11_c26_c5
    (hMp : GGInnerDiagMpInput)
    (hLB : GGLBalanceInput) (hTP : GGNbrTablePNbrInputOn GGRegimeA11) (hTCJ : GGTCJKnown)
    (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput) (hNS : GGNbrReflGenNonSplitInput) :
    GGSecFiveA11Input ∧ GGSecFiveCompatRestA11Input := by
  have h := ggSecFiveA11StrongInput_of_pieces hMp hLB hTP hTCJ hTB hRig hNS
    (a11FrameInput'_of_pieces (a11CoordInput_of_glue a11GlueExtInput_holds) a11TorusModelInput_holds
      a11LGenInput_holds a11FrameAssembleInput_holds)
    a11StrongOfDataInput_of_present
    (a11NbrInput'_of_pieces a11NbrLineInput_holds a11NbrInftyInput_holds a11NbrFrobInput_holds
      (a11NbrBadInput_of_pieces a11NbrLabelInput_holds a11NbrReflGenInput_holds
        a11NbrBadA8Input_holds a11NbrBadReflInput_holds a11AMatInput_holds a11A8HomolInput_holds
        a11ReflFixInput_holds a11SylowSplitInput_holds a11LemmaRInput_holds a11BadFixInput_holds))
  exact ⟨ggSecFiveA11Input_of_strong h, ggSecFiveCompatRestA11Input_of_strong h⟩

end CFSG.StandardType.A11

end
