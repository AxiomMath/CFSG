module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def E9Closed (X : Type*) [Group X] : Prop :=
  ∀ x : X, x ^ 3 = 1 → x ≠ 1 → ∃ y : X, y ^ 3 = 1 ∧ x * y = y * x ∧ y ∉ Subgroup.zpowers x

theorem E9Closed.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (hY : E9Closed Y) (e : X ≃* Y) :
    E9Closed X := by
  intro x hx3 hx1
  obtain ⟨y, hy3, hxy, hy⟩ := hY (e x) (by rw [← map_pow, hx3, map_one])
    (fun h => hx1 (e.injective (h.trans (map_one e).symm)))
  refine ⟨e.symm y, by rw [← map_pow, hy3, map_one], e.injective ?_, fun h => hy ?_⟩
  · rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hxy
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk, MulEquiv.apply_symm_apply]⟩

@[expose] def KF82E9GTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Odd n → Nat.card K = 2 ^ n →
    E9Closed (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)

@[expose] def KF82E9PGUThree : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), Odd n → IsoPGUThree X (2 ^ n) → E9Closed X

@[expose] def KF82E9ReeF4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), Odd n → CFSG.Blueprint.ReeTitsModel X .twistedF4 2 n →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ KFacts.IsInnerAut α → E9Closed (Sec4.autFix α)

@[expose] def KF82E9TrialityD4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ KFacts.IsInnerAut α → E9Closed (Sec4.autFix α)

section Kinds


@[expose] def KF82LThreeWrong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (n : ℕ), Even n → 1 ≤ n →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) → x ^ 3 = 1 →
      (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) →
        E9Closed (barCentralizer (Subgroup.zpowers x) L)

@[expose] def KF82OddSLThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (p e : ℕ) [Fact p.Prime],
    3 < p → 1 ≤ e → e ≤ 2 →
      (Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
        Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) → x ^ 3 = 1 →
      ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

@[expose] def KF82SLThreeFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (K : Type) [Field K] [Finite K],
    Nat.card K = 4 →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) →
      x ^ 3 = 1 → ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

end Kinds

end CFSG.RankThree.PartTwo.Sec8
