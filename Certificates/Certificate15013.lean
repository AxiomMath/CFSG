module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24Orders
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24OrdersData
import Certificates.Kernel.Fi23O4.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime in
theorem certificate15013 : fi23FourCheck fi23FourSlp fi23FourX fi23FourZ = true := KernelFi23O4.four_ok

end Certificates
