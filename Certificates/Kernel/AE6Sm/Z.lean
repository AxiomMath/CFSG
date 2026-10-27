module

public import Certificates.Kernel.AE6Q8.Cls
public import Certificates.Kernel.OmegaEight.Arr3009K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Sm

theorem ch517503z : Nat.beq CertificateChecks.KernelAE6Q8.SK.Z
    (CertificateChecks.KernelO8.mainK 0) = true := by quickRfl

end CertificateChecks.KernelAE6Sm

end
