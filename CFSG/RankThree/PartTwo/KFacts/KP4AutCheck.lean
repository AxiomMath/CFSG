module

public import CFSG.RankThree.PartTwo.KFacts.KP4Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import CFSG.RankThree.PartTwo.KFacts.KP4Data
public import CFSG.RankThree.PartTwo.KFacts.KP4AutCheckInputs
public import Certificates.Certificate8164

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open CFSG.ComponentClassification.WittDesign

theorem ofTab_deltaTab : ∀ p, ofTab deltaTab p = CFSG.Sporadic.Schreier.m22Delta p := by
  decide +kernel

theorem kp4_outer_count :
    m22Count (fun f => (∀ p, f (ofTab deltaTab (ofTab (lineTab 0) p)) =
        ofTab (lineTab 0) (f (ofTab deltaTab p))) ∧
      ∀ p, f (ofTab deltaTab (ofTab (lineTab 1) p)) =
        ofTab (lineTab 1) (f (ofTab deltaTab p))) = 0 :=
  Certificates.certificate8164

end CFSG.RankThree.PartTwo.KFacts.KP4
