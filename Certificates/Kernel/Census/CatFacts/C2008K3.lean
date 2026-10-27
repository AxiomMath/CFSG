
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

theorem cfCardS2008K :
    ((elemsV QS8).filter fun x => decide (x * (cfTau * cfZ) = cfTau * cfZ * x)).length =
      2 ^ 7 * 3 ∧
    ((elemsV QS8).filter fun x => decide (x * cfZ = cfZ * x)).length = 2 ^ 6 * 3 := by
  constructor <;> decide +kernel

theorem cfECent2008K : (elemsV QS8).all (fun x => !(cfEgens.all fun e =>
    decide (e * x = x * e)) || siftP cfQE x 0) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts
