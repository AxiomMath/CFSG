module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAutTests
import Certificates.Kernel.LocalComp.SixAut

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15062 : CFSG.ComponentClassification.RankTwoAlt.sixAutCheck = true := KernelLC.SixAut.sixAutCheck_eq

end Certificates
