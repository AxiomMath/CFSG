module

public import CFSG.RankThree.PartTwo.Sec21.Item211

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)

@[expose] def Item2131Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      (∃ n : ℕ, 0 < n ∧ Even n ∧ (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨
          Nonempty (lBar L ≃* projSU 4 2 n) ∨ Nonempty (lBar L ≃* SL3 n))) ∨
        Nonempty (lBar L ≃* projSU 5 2 2)

@[expose] def SU54LocalRankFive : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Group.IsPerfect Q → Nat.card (Subgroup.center Q) = 5 →
    Nonempty (Q ⧸ Subgroup.center Q ≃* projSU 5 2 2) → 3 ≤ localRank 5 Q

@[expose] def Item221SL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 → CFSG.IsQuasisimple L →
    Nonempty (lBar L ≃* SL3 2) → IsTypeCOnBarSL A L → IsPGroup 2 (aschbacherSolvableCore 3 L) →
    (∃ U' ∈ fourGroupsMinus E, U' ≤ L) →
      ∀ a ∈ A, a ∉ Subgroup.zpowers c →
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≠ ⊥ →
        Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≃*
          projSL 2 (GaloisField 2 2))

end CFSG.RankThree.PartTwo.Sec21
