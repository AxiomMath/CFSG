module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTests
import Certificates.Kernel.J4Q.FinkC2

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem certificate15040 : chkFinkC2 = true := KernelJ4Q.c15040

end Certificates
