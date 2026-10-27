module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvOrthOff
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvE7Off

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem noTransv_holds :
    NoTransv :=
  noTransv_of rowElemAb3_holds noTransvDataAt_D6 noTransvDataAt_twD7 noTransvDataAt_E7

theorem l1OddCore_holds :
    L1OddCore :=
  l1OddCore_of_split oddCoreTransvAt_D6 oddCoreTransvAt_twD7 oddCoreTransvAt_E7 noTransv_holds

end CFSG.StandardType.FrameRoute.FS81

end
