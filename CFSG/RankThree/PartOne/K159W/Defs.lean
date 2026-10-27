module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.RankThree.PartOne.K159W

@[expose] def WeylFive (K : Type) [Group K] : Prop :=
  ∃ R : Subgroup K, (∀ b ∈ R, b ^ 5 = 1) ∧ (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
    5 ^ 4 ≤ Nat.card R ∧
    (∃ n ∈ Subgroup.normalizer (R : Set K), n ^ 3 ∈ Subgroup.center K ∧ ∃ b ∈ R, n * b * n⁻¹ ≠ b) ∧
    (∃ n ∈ Subgroup.normalizer (R : Set K), n ^ 5 ∈ Subgroup.center K ∧ ∃ b ∈ R, n * b * n⁻¹ ≠ b)

@[expose] def ElemAbWeyl (p : ℕ) (K : Type) [Group K] : Prop :=
  (∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 5 ≤ Nat.card B) ∨
    (p = 5 ∧ WeylFive K)

@[expose] def CenterWeylFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.twoLocalOddRank X ≤ 3 → CFSG.IsKGroup X →
    ∀ (O : Subgroup X) [O.Normal], CFSG.IsQuasisimple (X ⧸ O) → ∀ p : ℕ, p.Prime → 3 < p →
      p ∣ Nat.card (Subgroup.center (X ⧸ O)) → Odd (Nat.card (Subgroup.center (X ⧸ O))) →
        ElemAbWeyl p (X ⧸ O)

end CFSG.RankThree.PartOne.K159W
