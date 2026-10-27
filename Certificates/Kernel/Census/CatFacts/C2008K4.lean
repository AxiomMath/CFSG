
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

theorem cfOrb22008K : (elemsV QS8).all (fun x => !(cfEgens.all fun e =>
      siftP cfQE (x * e * x⁻¹) 0) || (decide (x⁻¹ * cfZ * x ∈ cfOz.map Prod.fst) &&
      decide (x⁻¹ * (cfZ * cfTau) * x ∈ cfOzt.map Prod.fst))) = true ∧
    ((elemsV QS8).filter fun x => cfEgens.all fun e => siftP cfQE (x * e * x⁻¹) 0).length =
      1152 := by
  constructor <;> decide +kernel

end CertificateChecks.KernelCatFacts
