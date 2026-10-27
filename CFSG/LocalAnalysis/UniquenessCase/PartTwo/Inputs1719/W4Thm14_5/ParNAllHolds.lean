module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAll
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllLowRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllSL4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllSp6
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllOmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllOmegaMinusEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem kNatParNAll_holds : KNatParNAll := by
  intro W _ _ H S P k n hnat hk hperf hS hBP hPH hcomm hN
  refine nParam_eq_or_of_isNaturalClassicalModule_of_rankThree hnat hk hperf hS hBP hPH hcomm hN ?_
  rintro (h | h | h | h)
  · exact nParam_eq_of_natSL4 h hk hperf hS hBP hPH hcomm hN
  · exact nParam_eq_of_natOmegaPlusSix h hk hperf hS hBP hPH hcomm hN
  · exact nParam_eq_of_natSp6 h hk hperf hS hBP hPH hcomm hN
  · exact nParam_eq_of_natOmegaMinusEight h hk hperf hS hBP hPH hcomm hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
