module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesN7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortTwE6

public section

namespace CFSG.StandardType.RCKC1

theorem rckK2NbrRootSubShort_of_rest
    (h : RCKK2NbrRootSubShortRest) : RCKK2NbrRootSubShort := by
  refine rckK2NbrRootSubShort_of_at fun t' _ hS => ?_
  rcases hS with rfl | rfl | htw
  · exact rckK2NbrRootSubShortAt_PSp
  · exact rckK2NbrRootSubShortAt_F4
  · rcases htw with rfl | rfl | rfl
    · exact rckK2NbrRootSubShortAt_PSU
    · exact h
    · exact rckK2NbrRootSubShortAt_twistedE6

theorem ggSixRootCommKnownLeavesD1_of_n7
    (h : GGSixRootCommKnownLeavesN7) : GGSixRootCommKnownLeavesD1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, rckK2NbrRootSubShort_of_rest h4, h5, h6, h7, h8⟩

end CFSG.StandardType.RCKC1
