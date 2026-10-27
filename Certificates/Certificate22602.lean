module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs

public section

open CFSG.ComponentClassification.GHarris.SCert

namespace CertificateChecks.Batch22602

open CFSG.ComponentClassification.GHarris.SCert

private theorem conj_ya3_0 : ∀ w : SE, w * SE.invRep 1 = SE.invRep 1 * w → w ^ 4 = SE.gen 0 →
    ∃ s : SE, s⁻¹ * (SE.gen 7 * SE.gen 4) * s = w := by
  decide +kernel

end CertificateChecks.Batch22602

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22602 : ∀ w : SE, w * SE.invRep 1 = SE.invRep 1 * w → w ^ 4 = SE.gen 0 →
    ∃ s : SE, s⁻¹ * (SE.gen 7 * SE.gen 4) * s = w := by
  exact CertificateChecks.Batch22602.conj_ya3_0

end Certificates
