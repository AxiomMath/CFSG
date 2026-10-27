module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Facts
import Certificates.Kernel.Fi23Y.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Fi23 in
theorem certificate15011 : Fi23CensusFacts := KernelFi23Y.fi23_facts

end Certificates
