module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.MinusModel
public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.CaseAFactsOfModel
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.MinusField
import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
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
import CFSG.ClassicalGroups.Orthogonal.MinusCongr

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld

theorem o4CaseAFacts_of_mulEquiv_orthogonalMinus {X : Type} [Group X] {F : Type} [Field F]
    [Finite F] [CharP F 2] {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f) {b c : F}
    (hirr : ∀ t : F, t ^ 2 + b * t + c ≠ 0)
    (e : X ≃* ↥(CFSG.PGLModel.orthogonalMinus 1 F b c)) {s : X} (hs : s * s = 1)
    (hgen : Subgroup.closure {x | IsConj s x} = ⊤)
    (hprim : ∀ B : Set X, B ⊆ {x | IsConj s x} → B.Nonempty →
      (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨
        Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = {x | IsConj s x}) :
    O4CaseAFacts X {x | IsConj s x} := by
  obtain ⟨K, hK, hfin, hchar, D, ι, hιb, hιc, hcardK⟩ :=
    exists_hermInvol_of_irreducible hirr
  have hKF : Nat.card D.F = Nat.card F := (Nat.card_congr ι.toEquiv).symm
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : 4 ≤ Nat.card K := by
    rw [hcardK]
    nlinarith [hF4]
  have h4DF : 2 < Nat.card D.F := by
    rw [hKF, hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨ω, hω0, hω1⟩ :=
    CFSG.Timmesfeld.Bridge.Higman.exists_ne_zero_ne_one (K := D.F) h4DF
  let e' : X ≃* ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) :=
    e.trans (CFSG.ClassicalGroups.Orthogonal.orthogonalMinusCongr ι 1 hιb hιc)
  have hcover : ∀ (E : Type) [Group E] [Finite E]
      (p : E →* Matrix.SpecialLinearGroup (Fin 2) K),
      Function.Surjective p → p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥ := by
    intro E _ _ p hp hcen hE
    have hPerf : Group.IsPerfect E := by
      rw [Group.isPerfect_def]
      exact hE
    have hk : Nat.card K = 2 ^ (2 * f) := by
      rw [hcardK, hF, ← pow_mul]
      congr 1
      omega
    exact CFSG.LocalAnalysis.EvenBN.Common.ker_eq_bot_of_perfect_central_sl2_two_pow
      (m := 2 * f) (by omega) hk hp hcen
  exact o4CaseAFacts_of_mulEquiv e' (index_minusN D h4)
    (commutator_orthogonalMinus_one D h4) (commutator_minusN_eq_top D h4)
    (minusNEquiv D h4) hcover
    (fun t ht htN => isConj_RgO_of_mul_self_eq_one D h4 ht htN)
    (exists_triple_RgO D h4 hω0 hω1) hs hgen hprim

end CFSG.OddTranspositions.PartFour
