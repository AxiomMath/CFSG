module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalCriterionFromLeastFailure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairGenerationDischarge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndex

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.ProperTwoGeneratedCore CFSG.ProperTwoGeneratedCore.HighRankPair

theorem not_minimalLocalFailure_of_theoremTwo (hT : Assembly.TheoremTwo) (G : Type) [Group G]
    [Finite G] (H : Subgroup G) (z : G) : ¬ MinimalInvolutionPointLocalFailure H z :=
  fun h => h.failure (hT G H z h.local_datum h.central_sylow)

theorem shult_simple_of_theoremTwo (hT : Assembly.TheoremTwo)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) : fusionIsBenderGroup G :=
  shult_simple_of_no_least_failure (not_minimalLocalFailure_of_theoremTwo hT) G hnonab T U hUT
    hU hUel hclosed hTI

theorem shult_simple_of_solvableLinearCoset
    (h : ∀ (G : Type) [Group G] [Finite G], SolvableLinearCosetNormalizerTheorem G)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) : fusionIsBenderGroup G :=
  shult_simple_of_theoremTwo
    (theoremTwo_of_solvable_and_monomial fun G _ _ =>
      ⟨h G, UnitaryPairIndex.unitaryMonomialTheorem G⟩)
    G hnonab T U hUT hU hUel hclosed hTI

end CFSG.ShultStronglyClosedTI
