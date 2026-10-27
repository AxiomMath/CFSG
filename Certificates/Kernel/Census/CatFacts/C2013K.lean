
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

theorem cent2013K : centTrivCheck (elemsV QS8) a8 b8 = true := by
  decide +kernel

theorem neg2013K : centTrivCheck (elemsV QS8) a8 a8 = false := by
  decide +kernel

theorem len2013K : (elemsV QS8).length = 40320 := by
  decide +kernel

end CertificateChecks.KernelCatFacts
