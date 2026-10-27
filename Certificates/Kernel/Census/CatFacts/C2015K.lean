
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public import CFSG.GH74.KGroups.Checks3
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkEnum

theorem s0452015K : siftP QA45 s045 0 = true := by
  decide +kernel

theorem ql452015K : schP QL45 = true ∧ orderV QL45 = 360 := by
  constructor <;> decide +kernel

theorem la2015K : siftP QP45 la1 0 = true ∧ siftP QP45 lb1 0 = true ∧ siftP QP45 lb2 0 = true ∧
    la1 * s045 = s045 * la1 ∧ lb1 * s045 = s045 * lb1 ∧ lb2 * s045 = s045 * lb2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem qq452015K : schP QQ45 = true ∧ orderV QQ45 = 32 := by
  constructor <;> decide +kernel

theorem g0452015K : (elemsV QQ45).all (fun q => siftP QQ45 (g045 * q * g045⁻¹) 0) = true ∧
    siftP QQ45 g045 0 = false ∧ siftP QQ45 (g045 * g045) 0 = true ∧ siftP QP45 g045 0 = true ∧
    siftP QP45 (s045 * (g045⁻¹ * s045 * g045)) 0 = true ∧
    (q0gens.all fun q => siftP QA45 q 0 && decide (q * s045 = s045 * q)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem neg2015K : orderV QQ45 ≠ 64 ∧ orderV QL45 ≠ 720 ∧ siftP QQ45 g045 0 ≠ true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end CertificateChecks.KernelCatFacts
