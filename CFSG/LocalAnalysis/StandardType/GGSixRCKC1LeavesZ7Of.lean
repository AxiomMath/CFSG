module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesZ7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmM
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeavesF8_of_z7
    (h : GGSixRootCommKnownLeavesZ7) : GGSixRootCommKnownLeavesF8 := by
  obtain ⟨h1, h2, h3, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, rckK2NbrRootSubShortAt_OmM, h5, h6, h7⟩

end CFSG.StandardType.RCKC1
