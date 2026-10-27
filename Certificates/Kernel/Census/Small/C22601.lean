module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.SCert in
theorem check22601 : ∀ s : SE, s * SE.invRep 1 = SE.invRep 1 * s →
    (∀ g : SE, g * SE.invRep 1 = SE.invRep 1 * g → g * s = s * g) →
    s = 1 ∨ s = SE.gen 0 ∨ s = SE.invRep 1 ∨ s = SE.invRep 1 * SE.gen 0 := by
  decide +kernel

end CertificateChecks.KernelCensus
