
module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCatFacts

open CFSG.Certificates.Kernel.CatFacts

theorem cntE2009K : cntE = (1920, true) := by decide +kernel

end CertificateChecks.KernelCatFacts
