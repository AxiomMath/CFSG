module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.Timmesfeld.Bridge.Asc72ZMain
public import CFSG.OddTranspositions.PartFour.Fourteen.ModelWreath
public import CFSG.OddTranspositions.PartFour.Fourteen.Steps
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
public import CFSG.OddTranspositions.PartFour.Statements
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aSec23Inputs
public import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isBenderGroup_quotient_of_disconnected
    (h88 : Theorem8_8Quot) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) (hdis : Disconnected (imageClass hC)) :
    CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) := by
  let X := Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)
  have hradX : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hNs => eq_bot_of_quotient_solvableRadical N hN hNs
  have hder : derivedSeries X 1 = derivedSeries X 2 := by
    rcases h88 G D hC hrad h3 hns with h | h
    · exact h
    · exact absurd h hW
  have hS : Setup X (imageClass hC) := setup_quotient hC hns
  rcases theoremOne X (imageClass hC) hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hradX
      (exists_subgroup_of_disconnected hS hdis) with hB | hWreath | hA
  · exact hB
  · obtain ⟨f, n, -, hn, ⟨e⟩⟩ := hWreath
    exact absurd hder (derivedSeries_one_ne_two_of_mulEquiv_l2Wreath hn e)
  · exact absurd hA (not_almostSimpleCase_of_derivedSeries hS hder)

end CFSG.OddTranspositions.PartThree.ElevenThree
