module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData
import Certificates.Kernel.LocalComp.Co1End

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
theorem certificate15049 : co1EndCheck co1EndD co1EndIdx co1EndDB = true := KernelLC.Co1End.cert15049

end Certificates
