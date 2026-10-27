module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4SCHolds
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4LibHolds

public section

namespace CFSG.StandardType

theorem ggF4TwoFacts_holds :
    GGF4TwoFacts :=
  ⟨ggF4TwoCentre_holds, ggF4TwoRankFour_holds, ggF4TwoInvolutionCommutes_holds,
    ggF4TwoOutTwo_holds, ggF4TwoSCNoTwoLocal_holds⟩

theorem ggL48F4TwoThreeConfigInput_holds :
    GGL48F4TwoThreeConfigInput :=
  ggL48F4TwoThreeConfigInput_of_facts ggF4TwoFacts_holds

end CFSG.StandardType

end
