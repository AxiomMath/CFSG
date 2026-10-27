module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
import Certificates.Kernel.LocalComp.Co1Cen2B
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate2045

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
theorem certificate15045 : co1Cen2BCheck co1Cen2BH co1Cen2BUV co1Cen2BC co1Cen2BIC = true := KernelLC.Co1Cen2B.cert15045

end Certificates
