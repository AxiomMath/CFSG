module

public import Certificates.Kernel.Co1Syl5.Dag
public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Syl5

open CFSG.KC.Co1B (powWK eqK oneK)

theorem kP : (eqK (powWK (S.M 40) 5) oneK && eqK (powWK (S.M 38) 5) oneK) = true := by quickRfl

end CertificateChecks.KernelCo1Syl5

end
