module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankWithout
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingElementary
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingAlternatives
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelected
import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedMain

public section

namespace CFSG.RankThree.PartOne

theorem twoActionInputs_of_S9 : TwoActionInputs := by
  have hEFQKE := elementaryFaithfulQuotientKernelElimination
  have hMTASFQ := minimalTwoActionSmallFaithfulQuotient
  have hMTAWR3 := minimalTwoActionWithoutRankThreeFixedGroup_of hMTASFQ hEFQKE
  have hESAWGL := elementarySmallActionWholeGroupLifting_of hEFQKE
  have hMTAA := minimalTwoActionAlternatives_of hMTASFQ hEFQKE hESAWGL hMTAWR3
    minimalFiveActionSmallFieldKernelCentralization
  exact ⟨hMTAA, selectedPrimeMinimalTwoActionReduction_of hMTAA hMTASFQ hEFQKE, hESAWGL⟩

end CFSG.RankThree.PartOne
