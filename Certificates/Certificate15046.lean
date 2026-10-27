module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CData
import Certificates.Kernel.LocalComp.Co1Cen2C

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
theorem certificate15046 : co1Cen2CCheck co1Cen2CGlobal co1Cen2CS1 co1Cen2CS2 co1Cen2CD1 co1Cen2CD2 co1Cen2CZH1
    co1Cen2CZH2 co1Cen2CDec1 co1Cen2CDec2 co1Cen2CRD co1Cen2CRE = true := KernelLC.Co1Cen2C.cert15046

end Certificates
