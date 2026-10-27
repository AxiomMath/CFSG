
module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCatFacts

open CFSG.Certificates.Kernel.CatFacts CFSG.Certificates.Kernel.PkEnum
  CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem nA2009K : ((transL QA45).headD []).length = 45 := by decide +kernel

theorem cntZ2009K : cntZ = (1152, 192) := by decide +kernel

theorem allP2009K : allP = true := by decide +kernel

end CertificateChecks.KernelCatFacts
