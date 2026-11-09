module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinTabs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem sixChk1_false : sixChk1 false = true := by
  decide +kernel

theorem sixChk2_false : sixChk2 false = true := by
  rw [sixChk2_eq, sixInvProf_false_eq, sixInvAdj_eq]
  decide +kernel

theorem sixChk3_false : sixChk3 false = true := by
  rw [sixChk3_eq, sixInvProf_false_eq, sixInvAdj_eq]
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
