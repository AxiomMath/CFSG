module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusModel
public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.CaseAFactsOfModel
import CFSG.Timmesfeld.Bridge.RootStructR2Higman
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

namespace CFSG.OddTranspositions.PartFour

theorem o4CaseAFacts_of_mulEquiv_orthogonalPlus {X : Type} [Group X] {F : Type} [Field F]
    [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (e : X ≃* ↥(CFSG.PGLModel.orthogonalPlus 2 F)) {s : X} (hs : s * s = 1)
    (hgen : Subgroup.closure {x | IsConj s x} = ⊤)
    (hcover : ∀ (E : Type) [Group E] [Finite E]
      (p : E →* Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F),
      Function.Surjective p → p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥)
    (hprim : ∀ B : Set X, B ⊆ {x | IsConj s x} → B.Nonempty →
      (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨
        Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = {x | IsConj s x}) :
    O4CaseAFacts X {x | IsConj s x} := by
  have hcard : 2 < Nat.card F := by omega
  obtain ⟨ω, hω0, hω1⟩ :=
    CFSG.Timmesfeld.Bridge.Higman.exists_ne_zero_ne_one (K := F) hcard
  exact o4CaseAFacts_of_mulEquiv e (index_plusN (F := F))
    (commutator_orthogonalPlus_two h4) (commutator_plusN_eq_top h4)
    (plusNEquiv (F := F)) hcover
    (fun t ht htN => isConj_tauO_of_mul_self_eq_one ht htN)
    (exists_triple_tauO (F := F) hω0 hω1) hs hgen hprim

end CFSG.OddTranspositions.PartFour
