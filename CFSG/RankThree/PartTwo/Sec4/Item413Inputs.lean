module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Hyp413 {G : Type} [Group G] [Finite G] (L A E : Subgroup G) (c : G) : Prop :=
  SectionFourHyp G ∧ IsComponent L ∧ IsTriple413 L A E c ∧ 4 < CFSG.Open.pRank 3 A

@[expose] def IsSpecial413 (X : Type) [Group X] : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ Nonempty (X ≃* projSL 2 (GaloisField 3 e))) ∨
  (Nonempty (X ≃* projSL 3 (GaloisField 3 2)) ∨ Nonempty (X ≃* projSU 3 3 2)) ∨
  ((Nat.card (Subgroup.center X) = 3 ∧ Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)) ∨
    IsExtOf X Blueprint.NativeSporadic.McL (Multiplicative (ZMod 3))) ∨
  ((Nat.card (Subgroup.center X) = 3 ∧
      Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1) ∨
    IsExtOf X Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3))) ∨
  (Subgroup.center X = ⊥ ∧
    (Blueprint.ChevalleyExceptionalModel X .G2 3 1 ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (X ≃* projSU 4 3 1)))

structure Inputs413 : Prop where
  rankAutL2 : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f →
    CFSG.pRank 3 (MulAut (projSL 2 (GaloisField p f))) ≤ 3
  rankAutL3 : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f →
    CFSG.pRank 3 (MulAut (projSL 3 (GaloisField p f))) ≤ 3
  rankAutU3 : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f → 2 < p ^ f →
    CFSG.pRank 3 (MulAut (projSU 3 p f)) ≤ 3
  rankAutSL3 : ∀ (p f : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K], p ≠ 3 →
    Nat.card K = p ^ f → CFSG.pRank 3 (MulAut (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ≤ 3
  rankAutSU3 : ∀ (p f : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K], p ≠ 3 →
    Nat.card K = (p ^ f) ^ 2 → 2 < p ^ f →
      CFSG.pRank 3 (MulAut (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) ≤ 3
  rankAutSp4 : ∀ n : ℕ, 1 ≤ n → CFSG.pRank 3 (MulAut (projSp 2 (GaloisField 2 n))) ≤ 3
  rankAutG2 : ∀ (X : Type) [Group X] (n : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 n →
    CFSG.pRank 3 (MulAut X) ≤ 3
  rankAutF4 : ∀ (X : Type) [Group X] (n : ℕ), Blueprint.ReeTitsModel X .twistedF4 2 n →
    CFSG.pRank 3 (MulAut X) ≤ 3
  rankAutD4 : ∀ (X : Type) [Group X] (n : ℕ),
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n → CFSG.pRank 3 (MulAut X) ≤ 3
  rankG2 : ∀ (X : Type) [Group X] (p : ℕ) [Fact p.Prime], 3 < p →
    Blueprint.ChevalleyExceptionalModel X .G2 p 1 → CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3
  rankSp4 : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    CFSG.pRank 3 (projSp 2 (GaloisField p 1) ⧸ Subgroup.center (projSp 2 (GaloisField p 1))) ≤ 3
  rankU4 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    CFSG.pRank 3 (projSU 4 p 1 ⧸ Subgroup.center (projSU 4 p 1)) ≤ 3
  rankL4 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    CFSG.pRank 3 (projSL 4 (GaloisField p 1) ⧸ Subgroup.center (projSL 4 (GaloisField p 1))) ≤ 3
  rankU4Even : ∀ n : ℕ, 1 ≤ n →
    CFSG.pRank 3 (projSU 4 2 n ⧸ Subgroup.center (projSU 4 2 n)) ≤ 3
  rankA9 : CFSG.pRank 3 (alternatingGroup (Fin 9) ⧸ Subgroup.center (alternatingGroup (Fin 9))) ≤ 3
  rankSporadic : ∀ s ∈ sporadics46, s ≠ .McL →
    CFSG.pRank 3 (Blueprint.NativeSporadic.Carrier s ⧸
      Subgroup.center (Blueprint.NativeSporadic.Carrier s)) ≤ 3
  rankSeven : CFSG.pRank 3 (projSL 5 (GaloisField 2 1) ⧸
      Subgroup.center (projSL 5 (GaloisField 2 1))) ≤ 3 ∧
    CFSG.pRank 3 (projSp 3 (GaloisField 2 1) ⧸ Subgroup.center (projSp 3 (GaloisField 2 1))) ≤ 3 ∧
    CFSG.pRank 3 (projSU 5 2 2 ⧸ Subgroup.center (projSU 5 2 2)) ≤ 3
  rankEight : CFSG.pRank 3 (projSL 3 (GaloisField 3 1) ⧸
      Subgroup.center (projSL 3 (GaloisField 3 1))) ≤ 3 ∧
    CFSG.pRank 3 (projSU 3 3 1 ⧸ Subgroup.center (projSU 3 3 1)) ≤ 3
  rankTits : ∀ (X : Type) [Group X] (f : ℕ), Blueprint.ReeTitsModel X .Tits 2 f →
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3
  multiplier : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Nat.Coprime (Nat.card (Subgroup.center X)) 6 →
    (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSL 4 (GaloisField 3 1)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)) →
    Subgroup.center X = ⊥
  l2Three : ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    ∀ e : ℕ, 1 ≤ e →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 e)) →
      ∃ x ∈ E, ∃ m : ℕ, 2 < m ∧ Nonempty (L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        InducesStdKind L x .field
  l3Nine : ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 3 2)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 3 2) → False
  coverU43McL : ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G),
    Hyp413 L A E c →
    (Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 ∧
        Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* projSU 4 3 1)) ∨
      IsExtOf (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.McL
        (Multiplicative (ZMod 3)) →
    A ≤ L ∧ ∃ (K : Subgroup L) (_ : K.Normal), K.map L.subtype = Subgroup.zpowers c ∧
      (Nonempty (L ⧸ K ≃* projSU 4 3 1) ∨ Nonempty (L ⧸ K ≃* Blueprint.NativeSporadic.McL))
  coverG23ON : ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G),
    Hyp413 L A E c →
    (Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 ∧
        Blueprint.ChevalleyExceptionalModel ((L ⧸ aschbacherSolvableCore 3 L) ⧸
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1) ∨
      IsExtOf (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.ON
        (Multiplicative (ZMod 3)) → False

end CFSG.RankThree.PartTwo.Sec4
