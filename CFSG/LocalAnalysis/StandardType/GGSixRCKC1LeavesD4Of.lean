module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD4
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIp

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeavesShort_of_d4
    (h : GGSixRootCommKnownLeavesD4) :
    GGSixRootCommKnownLeavesShort := by
  obtain ⟨h1, h2, h3, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, CFSG.StandardType.RCKK1IIp.rckRowK1_IIp, h5, h6, h7, h8, h9, h10, h11⟩

end CFSG.StandardType.RCKC1
