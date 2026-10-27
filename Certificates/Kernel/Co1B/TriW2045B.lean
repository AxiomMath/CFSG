module

public import Certificates.Kernel.Co1B.TriW2045A
public meta import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

@[expose] noncomputable def w4 : Nat → Bool := wsl 4
@[expose] noncomputable def w5 : Nat → Bool := wsl 5
@[expose] noncomputable def w6 : Nat → Bool := wsl 6
@[expose] noncomputable def w7 : Nat → Bool := wsl 7
@[expose] noncomputable def w8 : Nat → Bool := wsl 8
@[expose] noncomputable def w9 : Nat → Bool := wsl 9
@[expose] noncomputable def w10 : Nat → Bool := wsl 10
@[expose] noncomputable def w11 : Nat → Bool := wsl 11

end CertificateChecks.KernelCo1B.Tri2045

#kc_slices CertificateChecks.KernelCo1B.Tri2045.W4 CertificateChecks.KernelCo1B.Tri2045.w4 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W5 CertificateChecks.KernelCo1B.Tri2045.w5 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W6 CertificateChecks.KernelCo1B.Tri2045.w6 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W7 CertificateChecks.KernelCo1B.Tri2045.w7 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W8 CertificateChecks.KernelCo1B.Tri2045.w8 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W9 CertificateChecks.KernelCo1B.Tri2045.w9 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W10 CertificateChecks.KernelCo1B.Tri2045.w10 11
#kc_slices CertificateChecks.KernelCo1B.Tri2045.W11 CertificateChecks.KernelCo1B.Tri2045.w11 11

end
