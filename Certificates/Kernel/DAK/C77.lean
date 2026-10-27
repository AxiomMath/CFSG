module

public import Certificates.Kernel.DAK.D77
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KD.DAK77

open Certificates.TWDK Certificates.DAK

theorem da77frame : kFrameOK 7 7 F = true := by decide +kernel

theorem da77cover : dakCover 7 S = true := by decide +kernel

theorem da77len : S.length = 18 := by decide +kernel

end CFSG.KD.DAK77

#kc_each CFSG.KD.DAK77 da77 (Certificates.DAK.dakSingleAt 7 7 CFSG.KD.DAK77.F CFSG.KD.DAK77.S) 0 18

end
