module

public import Certificates.Data.SmithL6TrDist
import Certificates.Kernel.SmithL6K.GlueD

public section

namespace Certificates

theorem certificate38682 : CFSG.SmithL6.trChkDist2 = true :=
  CertificateChecks.KernelSmithL6K.trChkDist2_holds

end Certificates
