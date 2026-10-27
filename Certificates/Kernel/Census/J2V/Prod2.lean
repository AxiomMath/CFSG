module

public import Certificates.Kernel.Census.J2V.Prod
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelJ2V

theorem prod2 : prodRows 64 32 = true := by quickRfl

end CertificateChecks.KernelJ2V
