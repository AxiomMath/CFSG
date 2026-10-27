module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLClassical
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFField
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFIn
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOut
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFRaw

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQTwoXInL_frame_formed_of
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) :
    GGQTwoXInLFrameFormed := by
  intro G _ _ B Bs x L D J hS hI hxL hA
  obtain ⟨hperf, lab, -, hraw⟩ := ggQTwoXInL_ambient_field hTCJ hRig hS hA
  obtain ⟨_, _, _, _, _, _, _, htag, hn, _⟩ := Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨R, _, I, F, hR, _, _, θ, _, _, hBs⟩ := exists_ggQTwoFRRecipe_of_rawDatum htag hn hraw
  obtain ⟨hBG, hcfg⟩ := ggQTwoFRCfg_of_marking hS hI hxL hR.1 θ hperf hBs
  exact ggQTwoXInL_frame_lift hLB hS hxL θ hBG (hR.2 _ _ _ _ _ hcfg)

end CFSG.StandardType

end
