module

public import CFSG.OddTranspositions.PartThree.EightEight.Statement
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.O4CloseReduction
public import Certificates.Certificate43
public import Certificates.Certificate113

import CFSG.OddTranspositions.FiveThreeQZ
import CFSG.OddTranspositions.PartThree.EightEight.OFourMinus
import CFSG.OddTranspositions.WidthOne
import CFSG.StronglyEmbedded.PSL2Facts

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72

@[expose] def EightEightCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    ¬ Group.IsSolvable (Halpha D hC.alpha) →
    FaithfulOnBlocks hC.alpha →
    ¬ CFSG.OddTranspositions.QZ.O4PairData G D →
    derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 =
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2

theorem theorem8_8Quot_of_core
    (h : EightEightCore) : Theorem8_8Quot := by
  intro G _ _ D hC hrad h3 hns
  by_cases hO4 : CFSG.OddTranspositions.QZ.O4PairData G D
  · exact Or.inl (derivedSeries_quot_solvableRadical_Halpha_of_o4PairData hC hO4)
  rcases CFSG.OddTranspositions.QZ.sixSix_dichotomy_of_rad hC hrad with hW | hF
  · exact Or.inr hW
  · exact Or.inl (h G D hC hrad h3 hns hF hO4)

end CFSG.OddTranspositions.PartThree.EightEight

end
