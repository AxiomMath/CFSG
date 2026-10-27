module

public import CFSG.RankThree.PartTwo.Sec4.Item47Statement

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Alt47W
    {G : Type} [Group G] [Finite G] (L : Subgroup G) (a : G) : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e))) ∧
      InducesStdKind L a .field) ∨
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
        IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) ∧
      InducesStdKind L a .diagonal) ∨
  (((∃ m : ℕ, 1 ≤ m ∧
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 m)) ∨
          (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 2 ∧
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
              CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 m) ∨
          ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * m) ∧
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
              CFSG.Assembly.LowTwoRank.StatedSL 3 K))) ∨
      ∃ n : ℕ, Odd n ∧
        (Blueprint.SuzukiModel (L ⧸ aschbacherSolvableCore 3 L) 2 n ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) ∨
          Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 n ∨
          Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 n)) ∧
      InducesStdKind L a .field) ∨
  (∃ n : ℕ, 1 ≤ n ∧
      (IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ n) ∨
        IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) 2 n) ∧
      InducesStdKind L a .diagonal) ∨
  (∃ n : ℕ, 1 ≤ n ∧
      Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 n)

@[expose] def Item4_7W :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → 3 ∣ Nat.card (Subgroup.center G) →
    ∀ L ∈ thetaComponents 3 G, ∀ a : G, orderOf a = 3 → InducesOuterTheta a L → Alt47W L a

theorem Alt47.toW
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G} (h : Alt47 L a) : Alt47W L a := by
  rcases h with h | h | h | h | ⟨n, -, hD4, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hD4.1.2.1, hD4⟩)))

theorem item4_7W_of_item4_7
    (h : Item4_7) : Item4_7W :=
  fun G _ _ hG h3 L hL a ha hout => (h G hG h3 L hL a ha hout).toW

end CFSG.RankThree.PartTwo.Sec4
