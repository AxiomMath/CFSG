module

public import CFSG.LocalAnalysis.StandardType.GGResIINoneg
public import CFSG.LocalAnalysis.StandardType.GGResIILinNoneg

public section

namespace CFSG.StandardType

theorem ggResIILinInput_holds : GGResIILinInput :=
  ggResIILinInput_of_noneg ggResIILinNonegInput_holds

end CFSG.StandardType
