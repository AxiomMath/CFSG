module

public import Certificates.Kernel.Co2Three.K
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CertificateChecks.KernelMisc.Co2K CFSG.RankThree.Native.F2

@[expose] noncomputable def ch13636G (ρ : ℕ) : Bool :=
  siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 (GM ρ)

end CertificateChecks.KernelCo2Three

#kc_each CertificateChecks.KernelCo2Three.ch13636G 0 8

namespace CertificateChecks.KernelCo2Three

#kc_forall_chunks ch13636G_all (fun ρ => ch13636G ρ = true) 8
  CertificateChecks.KernelCo2Three.ch13636G 1

end CertificateChecks.KernelCo2Three

end
