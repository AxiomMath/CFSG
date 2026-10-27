module

public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def EvenQ (X : Type) [Group X] : Prop := CFSG.Blueprint.EvenLieType X

@[expose] def KF64WWith (Q : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → CFSG.Assembly.evenRank H ≤ 3 →
    Group.IsPerfect H → ∀ p : ℕ, p.Prime → 7 ≤ p →
    CFSG.IsQuasisimple (H ⧸ aschbacherSolvableCore p H) →
    Q ((H ⧸ aschbacherSolvableCore p H) ⧸ Subgroup.center (H ⧸ aschbacherSolvableCore p H)) →
    ∀ E : Subgroup H, CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 3 →
      (∃ S : Subgroup H, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set H)) →
      (Nat.card (torusWeyl E)).factorization 3 ≤ 1

@[expose] def Item613With (Q : (X : Type) → [Group X] → Prop) : Prop :=
  SchreierFor InCatalog →
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → CFSG.Assembly.evenRank H ≤ 3 →
    ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ L ∈ thetaComponents p H, ∀ E : Subgroup H, CFSG.IsElementaryAbelian p E →
      p ^ 2 ≤ Nat.card E → E ≤ L →
      (∃ S : Subgroup H, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ L ∧
        ¬ S.subgroupOf L ≤ aschbacherSolvableCore p ↥L ∧
        E ≤ Subgroup.normalizer (S : Set H) ∧ ⁅S, E⁆ = S) →
      Q ((L ⧸ aschbacherSolvableCore p L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore p L))

theorem item613_iff_with : Item613 ↔ Item613With EvenQ := Iff.rfl

theorem kf64w_iff_with : KF64W ↔ KF64WWith EvenQ := Iff.rfl

end CFSG.RankThree.PartOne.N143
