module

public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
public import CFSG.OddTranspositions.PartThree.FiveReflection
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
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
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.OddTranspositions.PartFour.Statements
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aSec23Inputs
public import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.OddTranspositions.PartThree

theorem ascList_of_isFiveReflectionModel {X : Type} [Group X] {E : Set X} {n : ℕ} {ε π : Bool}
    (hn : 3 ≤ n) (h : IsFiveReflectionModel n ε π E) : AscList X E :=
  Or.inr (Or.inr (Or.inl ⟨n + 1, by omega, fischerModel_of_isFiveReflectionModel h⟩))

end CFSG.OddTranspositions.PartFour
