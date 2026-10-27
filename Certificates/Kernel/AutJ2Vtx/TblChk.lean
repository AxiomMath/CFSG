module

public import Certificates.Kernel.AutJ2Vtx.Tbl
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

theorem inv_ok : allN 22 (fun k => bAnd(canonK 315 9 (mask 9) (315 * 9) (AJT k),
    bAnd(canonK 315 9 (mask 9) (315 * 9) (AJI k),
      invEqK 315 9 (mask 9) (315 * 9) (AJT k) (AJI k)))) = true := by
  quickRfl

end CertificateChecks.KernelAJV

end
