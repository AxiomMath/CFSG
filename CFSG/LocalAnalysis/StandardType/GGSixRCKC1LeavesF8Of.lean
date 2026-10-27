module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSpinPlusFour

public section

namespace CFSG.StandardType.RCKC1

theorem ggSixRootCommKnownLeavesN7_of_f8
    (h : GGSixRootCommKnownLeavesF8) : GGSixRootCommKnownLeavesN7 := by
  obtain ⟨h1, h2, h3, h4, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4,
    CFSG.StandardType.RCKFlag.rckK2FlagRootSub_of_spinPlusFour
      CFSG.StandardType.RCKFlag.rckFlagSpinPlusFourOdd_holds, h6,
      rckRowK2_III_of_field_two (rckRowK2AtField_III_one_of_remaining h7), h8⟩

end CFSG.StandardType.RCKC1
