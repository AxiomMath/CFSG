module

public import Certificates.Kernel.C12643.CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC12643

@[expose] noncomputable def fC71 (a : Nat) : Bool := fC7 (Nat.add 80 a)

#lc_blocks c12643B5 fC71 80 1

end CertificateChecks.KernelC12643

end
