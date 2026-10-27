module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTri

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.RCKK1II

theorem ggSixRootCommKnownLeavesD2_of_d1
    (h : GGSixRootCommKnownLeavesD1) : GGSixRootCommKnownLeavesD2 := by
  obtain ⟨h1, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h8, h9⟩
  intro F _ _ σ hF
  exact rckRowIIAtTri_holds F σ hF

end CFSG.StandardType.RCKC1
