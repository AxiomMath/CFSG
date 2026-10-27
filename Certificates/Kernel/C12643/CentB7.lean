module

public import Certificates.Kernel.C12643.CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC12643

@[expose] noncomputable def fC73 (a : Nat) : Bool := fC7 (Nat.add 240 a)

#lc_blocks c12643B7 fC73 75 1

end CertificateChecks.KernelC12643

end
