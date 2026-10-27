module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIFinal

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeavesD3_of_d2
    (h : GGSixRootCommKnownLeavesD2) : GGSixRootCommKnownLeavesD3 := by
  obtain ⟨h1, hTri, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, CFSG.StandardType.RCKK1II.rckRowK1_II_of_tri LieOddCover.ggLieOddCover_holds hTri,
    h3, h4, h5, h6, h7, h8, h9⟩

end CFSG.StandardType.RCKC1
