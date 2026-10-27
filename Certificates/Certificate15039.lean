module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTests
import Certificates.Kernel.J4Q.FinkC1

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem certificate15039 : chkFinkC1 = true := KernelJ4Q.c15039

end Certificates
