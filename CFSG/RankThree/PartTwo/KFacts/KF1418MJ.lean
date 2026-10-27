module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)
open CFSG.RankThree.PartTwo (invariantPiSubgroups piOf)

@[expose] def KF1418MJ : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (K A R : Subgroup M) (e : M),
    (Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2)) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → A ≤ Subgroup.normalizer (K : Set M) →
    A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e →
    R ∈ invariantPiSubgroups K A (piOf 2) → ¬ R ≤ Sec4.thetaQuotCentralizer K →
      ∃ x ∈ A, ¬ ⁅inSubgroup (aschbacherSolvableCore 3)
        (K ⊓ Subgroup.centralizer ({x} : Set M)), A⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K

end CFSG.RankThree.PartTwo.KFacts
