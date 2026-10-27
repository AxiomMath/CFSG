module

public import Certificates.Data.CFSGNative.AS91.M24FixOct
import CFSG.Certificates.Kernel.M24G.FixOctSound
import Certificates.Kernel.M24G.FixOctReplay

public section

namespace Certificates

open CFSG.KC.M24G
open scoped CFSG.KC.M24G.FixOctEq

theorem certificate664001 : CFSG.Quasithin.H13.AS91.M24G.Native.fixOctPerfectCheck () = true :=
  fixOctPerfectCheck_of FixOctC.fixOctReplay_ok FixOctC.fixOctLen_ok FixOctC.fixOctComm_ok

end Certificates
