module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndK
import Certificates.Kernel.Sporadic.Suz.EndK
import Certificates.Kernel.Sporadic.Suz.EndEl

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Suz in
theorem certificate15038 : SuzEndFactsK :=
  KernelSpor.SuzEnd.suzEndFactsK_of KernelSpor.SuzEndEl.all

end Certificates
