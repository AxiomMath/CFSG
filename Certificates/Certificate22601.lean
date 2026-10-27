module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs
import Certificates.Kernel.Census.Small.C22601

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22601 : ∀ s : SE, s * SE.invRep 1 = SE.invRep 1 * s →
    (∀ g : SE, g * SE.invRep 1 = SE.invRep 1 * g → g * s = s * g) →
    s = 1 ∨ s = SE.gen 0 ∨ s = SE.invRep 1 ∨ s = SE.invRep 1 * SE.gen 0 := KernelCensus.check22601

end Certificates
