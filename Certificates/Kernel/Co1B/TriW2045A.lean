module

public import Certificates.Kernel.Co1B.TriD2045
public import Certificates.Data.Kernel.Co1BTri
public meta import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.KC.Co1T

@[expose] noncomputable def wsl (m s : Nat) : Bool := triWK (TB.T m) TB.PT (TB.P m) (s * 128) 128

@[expose] noncomputable def w0 : Nat → Bool := wsl 0
@[expose] noncomputable def w1 : Nat → Bool := wsl 1
@[expose] noncomputable def w2 : Nat → Bool := wsl 2
@[expose] noncomputable def w3 : Nat → Bool := wsl 3

end CertificateChecks.KernelCo1B.Tri2045

#kc_slices CertificateChecks.KernelCo1B.Tri2045.W0 CertificateChecks.KernelCo1B.Tri2045.w0 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W1 CertificateChecks.KernelCo1B.Tri2045.w1 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W2 CertificateChecks.KernelCo1B.Tri2045.w2 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W3 CertificateChecks.KernelCo1B.Tri2045.w3 11

end
