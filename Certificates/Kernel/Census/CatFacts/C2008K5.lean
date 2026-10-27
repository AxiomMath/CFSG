
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum

theorem cfOuterS2008K : (elemsV QS8).all (fun y => !decide (y * y = 1) || siftP QA8 y 0 ||
    decide (y ∈ cfCls1C) || decide (y ∈ cfCls2C)) = true := by
  decide +kernel

theorem cfOuterA2008K : (elemsV QA8).all (fun y => !decide (y * y = 1) || decide (y = 1) ||
    decide (y ∈ cfICls1C) || decide (y ∈ cfICls2C)) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts
