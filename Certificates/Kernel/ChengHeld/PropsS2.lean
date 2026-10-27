module

public import Certificates.Kernel.ChengHeld.PropsAut
public import Certificates.Data.Kernel.ChengHeldS2StructK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeldS2 CFSG.KC.ChengHeldP
open CFSG.OddStandard.ChengHeldData CertificateChecks.KernelChengHeld

theorem p6138_s2cl : (clW 128 n2 [h2 0, h2 1, h2 2] 6 &&
    clW 128 n2 [h2 0, h2 1, h2 2, h2 3, h2 4] 6 && clW 128 n2 [h2 0, h2 1, h2 2, h2 5, h2 6] 6) =
    true := by
  quickRfl

theorem p6138_s2cm : s2CmW 128 n2 j2 h2 6 = true := by
  quickRfl

theorem p6138_s2 : s2RestW 128 n2 h2 6 = true := by
  quickRfl

end CertificateChecks.KernelChengHeld.P

end
