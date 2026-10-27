module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMM0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMM1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMM2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMM3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

theorem nGModelFacts_holds : NGModelFacts := by
  unfold NGModelFacts
  intro i
  fin_cases i
  · exact modelFacts915_zero
  · exact modelFacts915_one
  · exact modelFacts915_two
  · exact modelFacts915_three

end CFSG.LocalAnalysis.WeakClosure81.NGM
