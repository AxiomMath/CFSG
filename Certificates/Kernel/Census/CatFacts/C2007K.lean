
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8ModelInputs
public import CFSG.GH74.KGroups.Checks
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.Certificates.Kernel.PkEnum

theorem qs8_2007K : schP QS8 = true ∧ orderV QS8 = 40320 := by
  constructor <;> decide +kernel

theorem qa8_2007K : schP QA8 = true ∧ orderV QA8 = 20160 := by
  constructor <;> decide +kernel

theorem neg2007K : orderV QA8 ≠ 40320 := by
  decide +kernel

end CertificateChecks.KernelCatFacts
