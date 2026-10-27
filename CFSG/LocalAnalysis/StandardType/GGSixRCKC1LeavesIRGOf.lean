module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesIRG
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1I
import CFSG.LocalAnalysis.StandardType.GGLieOddCover

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeaves_of_irg
    (h : GGSixRootCommKnownLeavesIRG) :
    GGSixRootCommKnownLeaves := by
  obtain ⟨hIRG, hrest⟩ := h
  exact ⟨RCKK1I.rckRowK1_I_of LieOddCover.ggLieOddCover_holds hIRG, hrest⟩

end CFSG.StandardType.RCKC1
