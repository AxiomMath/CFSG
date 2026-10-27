module

public import Certificates.Data.GSThmBCatalog7CF24
import Certificates.Kernel.Sporadic.CF24.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.CF24 in
theorem certificate23003 : cf24PermCheck = true :=
  KernelSpor.CF24.check

end Certificates
