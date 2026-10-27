module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaM22
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaJ2
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaRu
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaG24

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Blueprint
open Hering214Even


theorem item214EvenThetaFacts_of
    (hG24 : ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .G2 2 2 →
      EvenThetaFacts X) :
    Item214EvenThetaFacts := by
  intro X _ _ h
  rcases h with ⟨⟨e⟩⟩ | h | h | h | h | h
  · exact evenThetaFacts_of_mulEquiv e evenThetaFacts_m22
  · exact evenThetaFacts_of_hs h
  · exact evenThetaFacts_of_j2 h
  · exact evenThetaFacts_of_ru h
  · exact evenThetaFacts_of_L42 h
  · exact hG24 X h


theorem item214EvenThetaFacts_holds : Item214EvenThetaFacts :=
  item214EvenThetaFacts_of fun _ _ _ h => evenThetaFacts_of_g24 h

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
