
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA6Inputs
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.A6
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups.A6
  CFSG.Certificates.Kernel.PkEnum

theorem exp2006K : expCheck (elemsV QA) = true := by
  decide +kernel

theorem diag2006K : diagCheck (elemsV QA) (elemsV QP) = true := by
  decide +kernel

theorem inner2006K : innerCheck (elemsV QA) (elemsV QP) = true := by
  decide +kernel

theorem noComm2006K : noCommCheck (elemsV QA) (elemsV QP) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts
