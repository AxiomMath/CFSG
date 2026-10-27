module

public import Certificates.Kernel.Co1OddB.Chk
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CertificateChecks.KernelCo1OddB.Cand3

@[expose] noncomputable def f (s : Nat) : Bool := candRow (24 + s)

end CertificateChecks.KernelCo1OddB.Cand3

#kc_slices CertificateChecks.KernelCo1OddB.Cand3.H CertificateChecks.KernelCo1OddB.Cand3.f 8

end
