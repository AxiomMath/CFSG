module

public import CFSG.Quasithin.H13.AS91Sec4TwoInputs
import CFSG.Certificates.Kernel.AS91K42Sound
import Certificates.Kernel.AS91K42.Orbit

public section

namespace Certificates

open CertificateChecks.KernelAS91K42

open CFSG.Quasithin.H13.AS91 in
theorem certificate89401 : Two.orbitOK42 () = true :=
  Certificates.Kernel.AS91K42.orbitOK42_of ch89401_q0 ch89401_o1 ch89401_o2 ch89401_o3
    ch89401_inv ch89401_part ch89401_cnt

end Certificates
