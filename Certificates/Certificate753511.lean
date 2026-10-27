module

public import Certificates.Data.CoreE1Mathieu
import Certificates.Kernel.LocalComp.M12E1.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate753511 : Certificates.CoreE1Perm.check Certificates.CoreE1Perm.m12E1Data = true := KernelLC.M12E1.m12_e1

end Certificates
