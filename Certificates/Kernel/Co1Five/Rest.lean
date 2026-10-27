module

public import Certificates.Kernel.Co1Five.Defs
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Five

open CFSG.KC.Co1Cl CFSG.KC.Co1B

#kc_each ch1023014eq 0 1

#kc_each ch1023014tree 0 5

#kc_each ch1023014sort 0 5

#kc_each ch1023014closed 0 5

theorem ch1023014forest0 : ch1023014forest = true := by quickRfl

theorem ch1023014seeds : bAnd(canAllK TS 3, Nat.beq (TS 2) oneK) = true := by quickRfl

theorem ch1023014layout : layoutK CH WL 3 NQ = true := by quickRfl

end CertificateChecks.KernelCo1Five

end
