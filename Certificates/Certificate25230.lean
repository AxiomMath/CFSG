module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueTabCheck
import Certificates.Kernel.Fi22Uq.Final

public section

namespace Certificates

theorem certificate25230 : CFSG.EvenSporadicStandard.TwoFi22.DS81.uqTabCertificate = true :=
  CertificateChecks.KernelFi22Uq.uq_ok

end Certificates
