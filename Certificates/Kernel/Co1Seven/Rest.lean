module

public import Certificates.Kernel.Co1Seven.Defs
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Seven

open CFSG.KC.Co1Cl CFSG.KC.Co1B

#kc_each ch1023013eq 0 1

theorem ch1023013seeds : bAnd(canAllK TS 3, Nat.beq (TS 2) oneK) = true := by quickRfl

theorem ch1023013layout : layoutK CH WL 3 4189 = true := by quickRfl

theorem ch1023013sne : (!Nat.beq (TS SN) oneK) = true := by quickRfl

end CertificateChecks.KernelCo1Seven

end
