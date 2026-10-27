module

public import Certificates.Data.T84S4
import Certificates.Kernel.T84S4.Facts

public section

namespace Certificates

theorem certificate442352 : Certificates.T84S4.Facts :=
  CertificateChecks.KernelT84S4.facts

end Certificates
