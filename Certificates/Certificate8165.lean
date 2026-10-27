module

public import CFSG.RankThree.PartTwo.KFacts.KP4Data
import Certificates.Kernel.LocalComp.WittA8165
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KP4 CFSG.ComponentClassification.WittDesign in
theorem certificate8165 :
    (∀ i : Fin 4, m22Count (fun f => ∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) =
      36) ∧
    (∀ i : Fin 4, m22Count (fun f => (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) ∧
      ∀ p, f (f (f (f p))) = p) = 4) ∧
    m22Count (fun f => 7 ≤ (Finset.univ.filter fun p => f p = p).card) = 1 ∧
    (∀ k : Fin 4, m22Count (fun f => ∀ p ∈ hep k, f p ∈ hep k) = 2520) ∧
    (∀ i : Fin 4, m22Count (fun f => ∀ p ∈ tri i, f p ∈ tri i) = 288) ∧
    hexOne ∈ hexadList ∧ hexTwo ∈ hexadList := KernelLC.Witt.facts8165

end Certificates
