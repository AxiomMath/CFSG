module

public import CFSG.Quasithin.H13.AS91Sec4TwoInputs
import Certificates.Kernel.AS91S42.Checks
import CFSG.Certificates.Kernel.AS91S42Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.AS91 in
theorem certificate89402 : Two.stabOK42 () = true :=
  Certificates.Kernel.AS91S42.stabOK42_of KernelAS91S42.ch89402_s1 KernelAS91S42.ch89402_s2

end Certificates
