module

public import Certificates.Data.TitsFiveLocal
import Certificates.Kernel.MaxD2.TitsD.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19760 : Certificates.MaxD2Perm.check Certificates.MaxD2Perm.titsDData = true := KernelMaxD2.TitsD.titsD_check

end Certificates
