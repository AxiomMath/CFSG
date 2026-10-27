module

public import Certificates.Data.Y2L.HS
import Certificates.Kernel.Y2LHS.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.HigherRank.G2Three.Sec2 in
theorem certificate442315 : y2l_hsCheck () = true := KernelY2LHS.check

end Certificates
