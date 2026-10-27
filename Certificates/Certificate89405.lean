module

public import CFSG.Quasithin.H13.AS91Sec4FourInputs
import Certificates.Kernel.AS91K45.Checks44
import CFSG.Certificates.Kernel.AS91K45Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.AS91 in
theorem certificate89405 : Two.ok44 () = true :=
  Certificates.Kernel.AS91K45.ok44_of KernelAS91K45.ch89405_stab1 KernelAS91K45.ch89405_stab
    KernelAS91K45.ch89405_grp KernelAS91K45.ch89405_w5 KernelAS91K45.ch89405_perp

end Certificates
