module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def InnThetaNoncyclic {X : Type*} [Group X] (β : MulAut X) : Prop :=
  ∃ W V : Subgroup (MulAut X), Group.IsSolvable W ∧ ¬ 3 ∣ Nat.card W ∧
    W ≤ (MulAut.conj : X →* MulAut X).range ∧ (∀ w ∈ W, β * w = w * β) ∧
    (∀ y : X, β y = y → ∀ w ∈ W, MulAut.conj y * w * (MulAut.conj y)⁻¹ ∈ W) ∧
    V ≤ W ∧ IsPGroup 2 V ∧ ¬ IsCyclic V

@[expose] def IsChevTwo47 (X : Type) [Group X] : Prop :=
  ((∃ m : ℕ, 1 ≤ m ∧
      (Nonempty (X ≃* projSL 2 (GaloisField 2 m)) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 2 ∧
          Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) ∨
        Nonempty (X ≃* projSU 3 2 m) ∨
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * m) ∧
          Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K))) ∨
    ∃ n : ℕ, Odd n ∧
      (Blueprint.SuzukiModel X 2 n ∨
        Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
        Blueprint.ChevalleyExceptionalModel X .G2 2 n ∨
        Blueprint.ReeTitsModel X .twistedF4 2 n)) ∨
  ∃ n : ℕ, 1 ≤ n ∧ Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n

@[expose] def KLTwoCentralizer : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f → ∀ (X : Type) [Group X] [Finite X],
    Nonempty (X ≃* projSL 2 (GaloisField p f)) → ∀ β : MulAut X, orderOf β = 3 →
      InnThetaNoncyclic β → p = 3 ∧ f = 3 ∧ β ∉ (MulAut.conj : X →* MulAut X).range

@[expose] def KChevTwoCentralizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsChevTwo47 X →
    ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β

@[expose] def KSLThreeNoFieldKind :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (p e : ℕ) [Fact p.Prime],
    3 < p → 1 ≤ e → e ≤ 2 →
    (IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) → x ^ 3 = 1 →
    ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
