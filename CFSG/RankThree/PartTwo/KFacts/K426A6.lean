module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def McLThreeCentralizer : Prop :=
  ∀ x : Blueprint.NativeSporadic.McL, orderOf x = 3 →
    ∀ H : Subgroup Blueprint.NativeSporadic.McL, H ≤ Subgroup.centralizer {x} →
      ∀ f : H →* alternatingGroup (Fin 6), ¬ Function.Surjective f

@[expose] def J3CoverCentralizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) →
    ∀ y : X, y ∉ Subgroup.center X → y ^ 3 ∈ Subgroup.center X →
      ∀ P : Subgroup X, P ≤ Subgroup.centralizer {y} → Group.IsPerfect P →
        P ⊓ Subgroup.center X = ⊥

@[expose] def SLThreeFieldComponent : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 →
    ∀ α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K), α ^ 3 = 1 →
      (stdPinnedPSL 3 K).IsField (descendAut 3 K α) →
      ∀ P ∈ thetaComponentsIn (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _)),
        ¬ IsTripleCover (P ⧸ aschbacherSolvableCore 3 P) (alternatingGroup (Fin 6))

@[expose] def SUThreeFieldComponent : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K) (hq : 2 < p ^ f), p ≠ 3 →
    ∀ α : MulAut (unitarySU p f K 3), α ^ 3 = 1 →
      (stdPinnedPSU3 h).IsField (MulAut.congr (suCenterEquiv h hq) (centerDescend _ α)) →
      ∀ P ∈ thetaComponentsIn (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _)),
        ¬ IsTripleCover (P ⧸ aschbacherSolvableCore 3 P) (alternatingGroup (Fin 6))

end CFSG.RankThree.PartTwo.KFacts.K426
