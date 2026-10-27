module

public import Certificates.Kernel.Co2Three.K
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

#kc_each CertificateChecks.KernelCo2Three.ch13636Q 0 3

#kc_each CertificateChecks.KernelCo2Three.ch13636R 0 8

#kc_each CertificateChecks.KernelCo2Three.ch13636F 0 4

#kc_each CertificateChecks.KernelCo2Three.ch13636C 0 4

namespace CertificateChecks.KernelCo2Three

#kc_forall_chunks ch13636Q_all (fun j => ch13636Q j = true) 3
  CertificateChecks.KernelCo2Three.ch13636Q 1

#kc_forall_chunks ch13636R_all (fun ρ => ch13636R ρ = true) 8
  CertificateChecks.KernelCo2Three.ch13636R 1

#kc_forall_chunks ch13636F_all (fun j => ch13636F j = true) 4
  CertificateChecks.KernelCo2Three.ch13636F 1

#kc_forall_chunks ch13636C_all (fun j => ch13636C j = true) 4
  CertificateChecks.KernelCo2Three.ch13636C 1

end CertificateChecks.KernelCo2Three

end
