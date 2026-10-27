module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Ord27
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Norm7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Cent9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open SixteenEightKU43

theorem s16kU43SubgroupNoncyclic3_holds : S16kU43SubgroupNoncyclic3 :=
  s16kU43SubgroupNoncyclic3_of_facts u43NoOrder27 u43Cent5 u43Norm7 u43Cent9

theorem s16kU43Noncyclic3_holds : S16kU43Noncyclic3 :=
  s16kU43Noncyclic3_of_subgroup s16kU43SubgroupNoncyclic3_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
