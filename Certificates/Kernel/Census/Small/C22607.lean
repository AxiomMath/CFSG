module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisKCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.K3A5 in
theorem check22607 : ∀ a b : K, FourPair a b → nCard a b = 36 := by
  decide +kernel

end CertificateChecks.KernelCensus
