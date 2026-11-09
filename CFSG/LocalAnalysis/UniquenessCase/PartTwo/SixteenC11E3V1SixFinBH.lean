module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinTabs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem sixChk1_true : sixChk1 true = true := by
  decide +kernel

theorem sixChk2_true : sixChk2 true = true := by
  rw [sixChk2_eq, sixInvProf_true_eq, sixInvAdj_eq]
  decide +kernel

theorem sixChk3_true : sixChk3 true = true := by
  rw [sixChk3_eq, sixInvProf_true_eq, sixInvAdj_eq]
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
