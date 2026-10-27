module

public import Certificates.Kernel.Co3T.Orb
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co3T.EnumQ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3T

open CFSG.KC.Enum

theorem tpR0 : tailP (REP 0) = true := by quickRfl

theorem tpR1 : tailP (REP 1) = true := by quickRfl

theorem kOrb : allN 276 orbK = true := by quickRfl

end CertificateChecks.KernelCo3T

end
