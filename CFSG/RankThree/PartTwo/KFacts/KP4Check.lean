module

public import CFSG.RankThree.PartTwo.KFacts.KP4Data
public meta import CFSG.RankThree.PartTwo.KFacts.KP4Data
public import Certificates.Certificate8165
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open CFSG.ComponentClassification.WittDesign

theorem kp4_counts :
    (∀ i : Fin 4, m22Count (fun f => ∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) =
      36) ∧
    (∀ i : Fin 4, m22Count (fun f => (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) ∧
      ∀ p, f (f (f (f p))) = p) = 4) ∧
    m22Count (fun f => 7 ≤ (Finset.univ.filter fun p => f p = p).card) = 1 ∧
    (∀ k : Fin 4, m22Count (fun f => ∀ p ∈ hep k, f p ∈ hep k) = 2520) ∧
    (∀ i : Fin 4, m22Count (fun f => ∀ p ∈ tri i, f p ∈ tri i) = 288) ∧
    hexOne ∈ hexadList ∧ hexTwo ∈ hexadList :=
  Certificates.certificate8165

end CFSG.RankThree.PartTwo.KFacts.KP4
