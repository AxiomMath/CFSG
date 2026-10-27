module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisUTCertInputs
import Certificates.Kernel.Census.Small.C22605
import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23 in
theorem certificate22605 :
    (∀ s t : SE, s.d.val < 4 → t.d.val < 4 → SE.toUT (s * t) = SE.toUT s * SE.toUT t) ∧
    (∀ s : SE, s.d.val < 4 → SE.toUT s = 1 →
      s = 1 ∨ s = SE.gen 1 ∨ s = SE.gen 0 ∨ s = SE.gen 1 * SE.gen 0) ∧
    (∀ u : UT3 F4c, ∃ s : SE, s.d.val < 4 ∧ SE.toUT s = u) := KernelCensus.check22605

end Certificates
