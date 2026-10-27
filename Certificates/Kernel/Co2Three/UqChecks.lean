module

public import Certificates.Kernel.Co2Three.UqK
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

#kc_each CertificateChecks.KernelCo2Three.ch101704C 0 24

#kc_each CertificateChecks.KernelCo2Three.ch101704P 0 9

namespace CertificateChecks.KernelCo2Three

#kc_forall_chunks ch101704C_all (fun c => ch101704C c = true) 24
  CertificateChecks.KernelCo2Three.ch101704C 1

#kc_forall_chunks ch101704P_all (fun c => ch101704P c = true) 9
  CertificateChecks.KernelCo2Three.ch101704P 1

end CertificateChecks.KernelCo2Three

end
