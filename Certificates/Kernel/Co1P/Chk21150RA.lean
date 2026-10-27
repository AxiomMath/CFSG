module

public import Certificates.Kernel.Co1P.Defs21150S
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Co1PText
public import Certificates.Kernel.Co1P.Defs21150
public import Certificates.Kernel.Co1P.Defs21151
public import Certificates.Kernel.Co1P.Defs21154

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.Native

theorem recsA4_pin : recsEqK rA4 (recsT orbA4Masks) 0 = true := by quickRfl

theorem recsA4_lenB : Nat.beq (recsT orbA4Masks).length 60479 = true := by quickRfl

end CertificateChecks.KernelCo1P

end
