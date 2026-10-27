module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesShort
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesIRG
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeavesIRG_of_short
    (h : GGSixRootCommKnownLeavesShort) :
    GGSixRootCommKnownLeavesIRG := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, rckK2NbrRootSub_of rck_lemmaH_long h7, h8, h9, h10, h11⟩

end CFSG.StandardType.RCKC1
