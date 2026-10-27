module

public import Certificates.Kernel.Co1M.Data10071R
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Data.Kernel.Co1F2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CertificateChecks.KernelCo1Cover

@[expose] noncomputable def cmRP71 : List Nat := R0 :: R1 :: RP71

theorem cm71_prog_chk : progK 24 cmRP71 PROG71 2 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
