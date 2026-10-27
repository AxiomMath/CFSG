module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD3
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISU
import CFSG.LocalAnalysis.StandardType.GGLieOddCover

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeavesD4_of_d3
    (h : GGSixRootCommKnownLeavesD3) : GGSixRootCommKnownLeavesD4 := by
  obtain ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2,
    CFSG.StandardType.RCKK1IIISp.rckRowK1_III_of_su LieOddCover.ggLieOddCover_holds
      (CFSG.StandardType.RCKK1IIISU.rckRowK1IIISU_holds LieOddCover.ggLieOddCover_holds),
    h4, h5, h6, h7, h8, h9, h10⟩

end CFSG.StandardType.RCKC1
