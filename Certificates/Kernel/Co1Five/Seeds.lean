module

public import Certificates.Data.Kernel.Co1Three.Seeds
public import Certificates.Kernel.Co1Five.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Five

open CFSG.KC.Co1Cl

theorem ch1023014seedsBelow : seedsBelowK CH = true := by quickRfl

end CertificateChecks.KernelCo1Five

end
