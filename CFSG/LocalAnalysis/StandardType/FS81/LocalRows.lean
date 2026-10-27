module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.LocalModelE7

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem l1Local_holds :
    L1Local :=
  l1Local_of_rows l1LocalAt_D6 l1LocalAt_twD7 l1LocalAt_E7

end CFSG.StandardType.FrameRoute.FS81
