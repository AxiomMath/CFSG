module

public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Kernel.Co1M.Data10072
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Data.Kernel.Co1F2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CertificateChecks.KernelCo1Cover

@[expose] noncomputable def cmRP3 : List Nat := R0 :: R1 :: getL 0 cmRP71 27 :: RP3T

theorem cm_prog3_chk : progK 24 cmRP3 PROG3L 3 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
