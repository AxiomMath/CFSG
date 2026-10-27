module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcSix

public section

namespace CFSG.StandardType

theorem ggSecFiveBPermUniQTwoExcSixU62Input_holds :
    GGSecFiveBPermUniQTwoExcSixU62Input :=
  fun hU62 => ggSecFiveBPermUniQTwoExcSixInput_of_u62 ggLabelRigidInput_holds hU62

end CFSG.StandardType

end
