module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthFourHom

public section

namespace CFSG.StandardType


theorem ggSecFiveBCoordBOffQTwoOrthRouteInput_holds : GGSecFiveBCoordBOffQTwoOrthRouteInput :=
  ggSecFiveBCoordBOffQTwoOrthRouteInput_of_fourHom ggQTwoOrthFourHomInput_holds

end CFSG.StandardType

end
