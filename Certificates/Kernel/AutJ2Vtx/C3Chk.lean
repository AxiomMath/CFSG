module

public import Certificates.Kernel.AutJ2Vtx.Tbl
public import Certificates.Kernel.J2Cover.AutChain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelJ2Cover

theorem kC3 : (invEqK 315 9 (mask 9) (315 * 9) (AJT 12) (AJT 12) &&
    !siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 (AJT 12) &&
    invEqK 315 9 (mask 9) (315 * 9) (AJT 13) (AJT 13) &&
    !Nat.beq (pcomp 315 9 (mask 9) (AJT 13) (AJT 8)) (pcomp 315 9 (mask 9) (AJT 8) (AJT 13)) &&
    Nat.beq (pcomp 315 9 (mask 9) (AJT 12) (AJT 13)) (pcomp 315 9 (mask 9) (AJT 13) (AJT 12))) =
    true := by quickRfl

end CertificateChecks.KernelAJV

end
