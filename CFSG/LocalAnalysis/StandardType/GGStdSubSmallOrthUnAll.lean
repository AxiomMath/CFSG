module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourMain
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourOmega
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourU3

public section

namespace CFSG.StandardType

namespace SmallOrth

open SmallOrthUn

theorem plusTwoFourInput_holds : PlusTwoFourInput :=
  plusTwoFourInput_of omegaFourInput_holds unitaryThreeInput_holds

theorem minusUnitThreeInput_holds : MinusUnitThreeInput :=
  minusUnitThreeInput_of omegaFourInput_holds unitaryThreeInput_holds

theorem plusTwoInput_holds : PlusTwoInput :=
  plusTwoInput_of_vacuous_four plusTwoVacuousInput_holds plusTwoFourInput_holds

theorem minusUnitInput_holds : MinusUnitInput :=
  minusUnitInput_of_vacuous_three minusUnitVacuousInput_holds minusUnitThreeInput_holds

end SmallOrth

end CFSG.StandardType

end
