module

public import CFSG.LocalAnalysis.StandardType.GGResIQFour
public import CFSG.LocalAnalysis.StandardType.GGResILin

public section

namespace CFSG.StandardType

theorem ggResCaseIQFourInput_of_inputs (hFix : GGTBFixInput) (hJr : GGForkJr)
    (hPump : GGForkPumpOr) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hReal : GGReflRealizedQFourInputThree) (hPL : GGPumpLineThreeInput)
    (hO2 : GGResCaseIQFourO2Input) : GGResCaseIQFourInput :=
  ggResCaseIQFourInput_of_lin hFix hJr hPump hLB hSP hReal hPL hO2 ggResILinInput_holds

end CFSG.StandardType
