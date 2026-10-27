module

public import CFSG.RankThree.PartTwo.KFacts.KP4AutCheckInputs
import Certificates.Kernel.LocalComp.WittA8164

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KP4 CFSG.ComponentClassification.WittDesign in
theorem certificate8164 :
    m22Count (fun f => (∀ p, f (ofTab deltaTab (ofTab (lineTab 0) p)) =
        ofTab (lineTab 0) (f (ofTab deltaTab p))) ∧
      ∀ p, f (ofTab deltaTab (ofTab (lineTab 1) p)) =
        ofTab (lineTab 1) (f (ofTab deltaTab p))) = 0 := KernelLC.Witt.facts8164

end Certificates
