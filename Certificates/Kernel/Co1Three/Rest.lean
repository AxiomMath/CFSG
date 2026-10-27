module

public import Certificates.Kernel.Co1Three.Defs
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Co1Cl CFSG.KC.Co1B

#kc_each eqChunk 0 4

theorem seeds : bAnd(canAllK TS 12, Nat.beq (TS 11) oneK) = true := by quickRfl

theorem layout : layoutK CH WL 12 28098 = true := by quickRfl

theorem norm : normK TS 3 GL NZ = true := by quickRfl

theorem forest : forestK 3 6 NZ RT DP FT = true := by quickRfl

end CertificateChecks.KernelCo1Three

end
