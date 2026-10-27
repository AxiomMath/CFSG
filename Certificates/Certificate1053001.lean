module

public import Certificates.Data.J2CentEACheck
import Certificates.Kernel.GH74.J2CentEAF

public section

namespace Certificates

theorem certificate1053001 : CFSG.Sporadic.J2.j2CentEACheck = true :=
  CertificateChecks.KernelGH74.J2CentEA.check_ok

end Certificates
