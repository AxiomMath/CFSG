module

public import Certificates.Data.Kernel.Co1Three.Seeds
public import Certificates.Kernel.Co1Seven.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Seven

open CFSG.KC.Co1Cl

theorem ch1023013seedsBelow : seedsBelowK CH = true := by quickRfl

end CertificateChecks.KernelCo1Seven

end
