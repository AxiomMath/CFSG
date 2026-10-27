module

public import Certificates.Data.L34InnerLocal
import Certificates.Kernel.MaxD2.L34.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19767 : Certificates.MaxD2Perm.check Certificates.MaxD2Perm.l34InnerData = true := KernelMaxD2.L34.l34_check

end Certificates
