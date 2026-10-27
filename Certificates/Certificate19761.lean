module

public import Certificates.Data.TitsFiveLocal
import Certificates.Kernel.MaxD2.TitsA.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19761 : Certificates.MaxD2Perm.check Certificates.MaxD2Perm.titsAData = true := KernelMaxD2.TitsA.titsA_check

end Certificates
