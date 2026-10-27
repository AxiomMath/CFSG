module

public import Certificates.Kernel.Co1B.Data17590
public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Fix17590

open CFSG.KC.Co1F2 CFSG.KC.Co1B CertificateChecks.KernelCo1M

@[expose] noncomputable def C1K : Nat := mulWK (getL 0 cmRP71 27) (getL 0 cmRP71 73)

theorem fix_chk : fixK 24 (trK 24 C1K) 0 D.F D.Y 8 256 0 = true := by quickRfl

end CertificateChecks.KernelCo1B.Fix17590

end
