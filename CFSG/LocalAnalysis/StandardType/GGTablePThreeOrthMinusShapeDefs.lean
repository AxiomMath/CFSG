module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

abbrev POmMinusG (m : ℕ) (K : Type) [Field K] (b c : K) : Type :=
  LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))

@[expose] def OrthMinusShapeConcl {X : Type} [Group X] (n r : ℕ) (A : Subgroup (MulAut X))
    (J : Subgroup X) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) ∧
    ((lab.tag = .A ∧ (lab.rank = 1 → Nat.card A ≤ 3 ^ 2) ∧ (lab.rank = 2 → Subgroup.center J ≠ ⊥)) ∨
      (lab.tag = .twA ∧ (lab.rank = 2 → Subgroup.center J ≠ ⊥ ∧ r ≤ 4)) ∨ lab.tag = .B ∨ lab.tag = .C ∨
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ lab.n = n ∧
        (lab.tag = .D → lab.rank = 4 → Odd n → r = 5 ∨ (r = 7 ∧ n = 1))))

end CFSG.StandardType.TablePThreeKG

end
