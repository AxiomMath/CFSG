module

public import Certificates.Data.HarrisLitN36HS2C
import Certificates.Kernel.HS3850.H2CGlue

public section

namespace Certificates

theorem certificate22619 : CFSG.ComponentClassification.HarrisLit.N36.HS2C.hs2CCheck = true :=
  CertificateChecks.KernelHS3850.H2C.hs2CCheck_true

end Certificates
