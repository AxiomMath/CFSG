module

public import CFSG.Quasithin.H13.U3Confined
public import CFSG.LocalAnalysis.QuasithinUnique.TopNative

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.QuasithinUnique

theorem uniqueThreeCaseModelReduction_holds
    : UniqueThreeCaseModelReduction := by
  intro G _ _ T M h
  exact theorem_2_1_1_of_branches benderBranch constrainedBranch_proved
    unconstrainedBranch_proved h

end CFSG.Quasithin.H13.U3
