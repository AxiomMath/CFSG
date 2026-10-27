module

public import Certificates.Data.Kernel.Co1Three.Seeds
public import Certificates.Kernel.Co1Three.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Co1Cl

theorem seedsBelow : seedsBelowK CH = true := by quickRfl

end CertificateChecks.KernelCo1Three

end
