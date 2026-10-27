module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.List19
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Reduce

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily


theorem k_19_21_levi_holds : K_19_21_levi :=
  k_19_21_levi_of_hasLeviFamiliesAlt fun _ _ _ hS h => hasLeviFamiliesAlt_of_list19 hS h

theorem k_19_18_levi_holds : K_19_18_levi :=
  k_19_18_levi_of_hasLeviFamilies fun _ _ _ hS h =>
    (hasLeviFamiliesAlt_of_list19 hS h).hasLeviFamilies

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
