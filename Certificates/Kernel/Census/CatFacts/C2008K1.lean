
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

theorem cfCoset2008K : (elemsV QS8).all (fun x => !(q0gens.all fun q =>
    siftP QQ8 (x * q * x⁻¹) 0) || siftP QQ8 x 0 || siftP QQ8 (g08⁻¹ * x) 0) = true := by
  decide +kernel

theorem cfNorm2008K : (elemsV QS8).all (fun x => !(cfHgens.all fun h =>
    siftP cfQH (x * h * x⁻¹) 0) || siftP cfQR x 0) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts
