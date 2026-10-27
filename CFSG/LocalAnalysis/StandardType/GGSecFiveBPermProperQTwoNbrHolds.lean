module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpLeafDefs
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoNbrOfInputs

public section

namespace CFSG.StandardType

theorem ggSecFiveBPermProperQTwoNbrRedInput_holds :
    GGSecFiveBPermProperQTwoNbrRedInput :=
  fun hTBF hX hTCJ hTPn hA8 hraw hiso hFC hLB hRoot hT hLift hI3 hPJ hTE6R hCP =>
    ggSecFiveBPermProperQTwoNbrInput_of_inputs hTBF hX hTCJ ggLabelRigidInput_holds hTPn hA8
      hraw hiso hFC hLB hRoot hT hLift hI3 hPJ hTE6R hCP ggInnerDiagMpInput_holds

end CFSG.StandardType

end
