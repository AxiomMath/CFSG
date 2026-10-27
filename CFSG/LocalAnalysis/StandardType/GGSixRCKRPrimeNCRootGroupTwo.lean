module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassicalSpecs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePinnedTransfer

public section

namespace CFSG.StandardType.RCKRP

theorem rckRootGroupTwo_holds : RCKRootGroupTwo := by
  intro M g hM β hβ
  exact rootGroup_isPGroup_of_standardReturnAt hM hβ

end CFSG.StandardType.RCKRP

end
