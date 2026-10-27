module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ShultMilestoneAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerDischarge

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.qt_unique_shult_simple_strongly_closed_ti_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) :
    fusionIsBenderGroup G :=
  CFSG.ShultStronglyClosedTI.shult_simple_of_theoremTwo
    (CFSG.ProperTwoGeneratedCore.HighRankPair.theoremTwo_of_unitaryMonomial
      CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.unitaryMonomialTheorem)
    G hnonab T U hUT hU hUel hclosed hTI

end CFSG.Open
