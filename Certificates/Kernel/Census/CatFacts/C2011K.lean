
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34RankInputs
public import CFSG.GH74.KGroups.Checks3
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups

theorem qs_2011K : schP QS = true ∧ orderV QS = 20160 := by
  constructor <;> decide +kernel

theorem qe_2011K : schP QE = true ∧ orderV QE = 16 := by
  constructor <;> decide +kernel

theorem class_2011K : classCheck (elemsV QS) g₂ conjugators = true := by
  decide +kernel

theorem sq_2011K : sqOneCheck (elemsV QE) = true ∧ indepCheck g₂ g₃ c₁ = true := by
  constructor <;> decide +kernel

end CertificateChecks.KernelCatFacts
