module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpCases
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoRecFive
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoDefs
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinOmKFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSU
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUni
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniSpChart
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniFourVacuous
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwo

public section

namespace CFSG.StandardType


theorem ggSecFiveBPermOffSpInput_of_heads (hLN : GGSecFiveBPermLinNbrInput)
    (hQ4 : GGSecFiveBPermQTwoRecFourInput) (hSU : GGSecFiveBPermSURecInput)
    (hUN : GGSecFiveBPermUniNbrInput) (hO : GGSecFiveBPermUniOmInput)
    (hQN : GGSecFiveBPermUniQTwoNbrInput) (hQS : GGSecFiveBPermUniQTwoSpInput)
    (hQO : GGSecFiveBPermUniQTwoOmInput) (hQX : GGSecFiveBPermUniQTwoExcInput)
    (hPN : GGSecFiveBPermProperNbrInput) (hPN2 : GGSecFiveBPermProperQTwoNbrInput)
    (hPP2 : GGSecFiveBPermProperQTwoSpPairInput) (hJ : BMaxJoinInput) :
    GGSecFiveBPermOffSpInput :=
  ggSecFiveBPermOffSpInput_of_cases
    (ggSecFiveBPermOffSpLinInput_of_rows hJ hLN
      (ggSecFiveBPermOmChartInput_of_mp ggInnerDiagMpInput_holds)
      (ggSecFiveBPermQTwoRecInput_of_mp ggInnerDiagMpInput_holds hQ4)
      (ggSecFiveBPermSUDataInput_of_rec hJ hSU))
    (ggSecFiveBPermOffSpUniInput_of_rows hUN
      (ggSecFiveBPermUniSpChartInput_of_mp ggInnerDiagMpInput_holds) hO
      ggSecFiveBPermUniFourInput_holds (ggSecFiveBPermUniQTwoInput_of_rows hQN hQS hQO hQX hJ) hJ)
    (ggSecFiveBPermOffSpProperInput_of_allRows hPN
      (ggSecFiveBPermUniSpChartInput_of_mp ggInnerDiagMpInput_holds) hO hPN2 hQS hQO hPP2 hJ)

end CFSG.StandardType

end
