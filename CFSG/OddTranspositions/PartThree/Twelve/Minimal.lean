module

public import CFSG.OddTranspositions.PartThree.Twelve.One
public import CFSG.OddTranspositions.PartFour.Fourteen.TheoremFourPrinted
public import CFSG.CGT.T75E.Lemma26
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aSec23Inputs
public import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81

@[expose] def Theorem4Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Nat.card G < n →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    (¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
    TheoremFourConclusion hC

theorem theorem4_of_step (h91 : Theorem9_1) (h101 : Theorem10_1) (h111 : Theorem11_1)
    (h112 : Theorem11_2)
    (h : ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
      Theorem4Below (Nat.card G) →
      (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
      CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
      (¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
        IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
      TwelveOneShape hC → TheoremFourConclusion hC) :
    Theorem4 := by
  have key : ∀ n, Theorem4Below n := by
    intro n
    induction n with
    | zero => exact fun G _ _ D hC hlt => absurd hlt (Nat.not_lt_zero _)
    | succ n ih =>
      intro G _ _ D hC hlt hrad hE hMZ hO4
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      · exact ih G D hC hlt' hrad hE hMZ hO4
      · rcases twelveOne h91 h101 h111 h112 hC hrad hE hMZ hO4 with h1 | h1
        · exact h1
        · exact h G D hC (heq ▸ ih) hrad hE hMZ hO4 h1
  intro G _ _ D hC hrad hE hMZ hO4
  exact key (Nat.card G + 1) G D hC (Nat.lt_succ_self _) hrad hE hMZ hO4

end CFSG.OddTranspositions.PartThree

end
