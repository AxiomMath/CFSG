module

public import CFSG.Quasithin.H13.AS91Sec4FiveInputs
import Certificates.Kernel.AS91K45.Checks45
import CFSG.Certificates.Kernel.AS91K45Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.AS91 in
theorem certificate89404 : Two.ok45 () = true :=
  Certificates.Kernel.AS91K45.ok45_of KernelAS91K45.ch89404_stab1 KernelAS91K45.ch89404_orb
    KernelAS91K45.ch89404_stab KernelAS91K45.ch89404_p

end Certificates
