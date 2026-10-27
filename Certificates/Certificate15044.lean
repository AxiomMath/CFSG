module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2ATests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2AData
import Certificates.Kernel.LocalComp.Co1Cen2A

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
theorem certificate15044 : co1Cen2ACheck co1Cen2AGlobal co1Cen2AS1 co1Cen2AS2 co1Cen2AD1 co1Cen2AD2 co1Cen2AZH1
    co1Cen2AZH2 co1Cen2ADec1 co1Cen2ADec2 co1Cen2AQD co1Cen2AQE = true := KernelLC.Co1Cen2A.cert15044

end Certificates
