module

public import Certificates.Kernel.DAK.D510
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KD.DAK510

open Certificates.TWDK Certificates.DAK

theorem da510frame : kFrameOK 5 10 F = true := by decide +kernel

theorem da510cover : dakCover 10 S = true := by decide +kernel

theorem da510len : S.length = 16 := by decide +kernel

end CFSG.KD.DAK510

#kc_each CFSG.KD.DAK510 da510
  (Certificates.DAK.dakSingleAt 5 10 CFSG.KD.DAK510.F CFSG.KD.DAK510.S) 0 16

end
