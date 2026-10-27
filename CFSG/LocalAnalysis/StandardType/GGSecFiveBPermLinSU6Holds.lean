module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpLeafDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinSU6

public section

namespace CFSG.StandardType

theorem ggSecFiveBPermLinSU6BalInput_holds :
    GGSecFiveBPermLinSU6BalInput :=
  ggSecFiveBPermLinSU6Input_of_balance

end CFSG.StandardType

end
