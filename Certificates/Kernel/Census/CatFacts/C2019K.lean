
module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8PermInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.GSThmB.A8 CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum

theorem tau2019K : tauCheck (elemsV QA8) t15 = true := by
  decide +kernel

theorem n3_2019K : n3Check (elemsV QL8) QL8 n3Data = true := by
  decide +kernel

theorem n4_2019K : n4Check (elemsV QS8) (elemsV QA8) t15 = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts
