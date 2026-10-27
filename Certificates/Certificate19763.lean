module

public import Certificates.Data.M11ThreeLocal
import Certificates.Kernel.MaxD2.M11.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19763 : Certificates.MaxD2Perm.check Certificates.MaxD2Perm.m11ThreeData = true := KernelMaxD2.M11.m11_check

end Certificates
