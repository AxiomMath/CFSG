module

public import Certificates.Data.SolMaxH35J2
import Certificates.Kernel.J2H35.Glue

public section

namespace Certificates

open CFSG.ComponentClassification.SolMax.H35.J2 in
theorem certificate23301 : j2H35Check = true :=
  CertificateChecks.KernelJ2H35.j2H35Check_true

end Certificates
