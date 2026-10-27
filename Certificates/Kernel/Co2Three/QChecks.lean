module

public import Certificates.Kernel.Co2Three.QK
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

#kc_each CertificateChecks.KernelCo2Three.ch13636QP 0 9

#kc_each CertificateChecks.KernelCo2Three.ch13636QK 0 9

#kc_each CertificateChecks.KernelCo2Three.ch13636QR 0 1

#kc_each CertificateChecks.KernelCo2Three.ch13636H 0 16

#kc_each CertificateChecks.KernelCo2Three.ch13636Fus 0 9

#kc_each CertificateChecks.KernelCo2Three.ch13636S 0 7

#kc_each CertificateChecks.KernelCo2Three.ch13636D 0 1

namespace CertificateChecks.KernelCo2Three

#kc_forall_chunks ch13636QP_all (fun c => ch13636QP c = true) 9
  CertificateChecks.KernelCo2Three.ch13636QP 1

#kc_forall_chunks ch13636QK_all (fun c => ch13636QK c = true) 9
  CertificateChecks.KernelCo2Three.ch13636QK 1

#kc_forall_chunks ch13636QR_all (fun c => ch13636QR c = true) 1
  CertificateChecks.KernelCo2Three.ch13636QR 1

#kc_forall_chunks ch13636H_all (fun i => ch13636H i = true) 16
  CertificateChecks.KernelCo2Three.ch13636H 1

#kc_forall_chunks ch13636Fus_all (fun c => ch13636Fus c = true) 9
  CertificateChecks.KernelCo2Three.ch13636Fus 1

#kc_forall_chunks ch13636S_all (fun j => ch13636S j = true) 7
  CertificateChecks.KernelCo2Three.ch13636S 1

#kc_forall_chunks ch13636D_all (fun c => ch13636D c = true) 1
  CertificateChecks.KernelCo2Three.ch13636D 1

end CertificateChecks.KernelCo2Three

end
