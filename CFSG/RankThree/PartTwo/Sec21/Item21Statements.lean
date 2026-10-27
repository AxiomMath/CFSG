module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

@[expose] def Item212 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsL4L5Sp6 L →
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

@[expose] def Item213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → CFSG.IsQuasisimple L

@[expose] def Item214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
      ((∃ U' ∈ fourGroupsMinus E, U' ≤ L) ↔
        ¬ ∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n))

@[expose] def Item217 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsEmpty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3)

@[expose] def Item218 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
      IsEmpty (lBar L ≃* NativeSporadic.M24) ∧ IsEmpty (lBar L ≃* NativeSporadic.He) ∧
      IsEmpty (lBar L ≃* NativeSporadic.J2) ∧ IsEmpty (lBar L ≃* NativeSporadic.Ru) ∧
      IsEmpty (lBar L ≃* NativeSporadic.J4) ∧
      (∀ n : ℕ, ¬ ChevalleyExceptionalModel (lBar L) .G2 2 n) ∧
      ∀ n : ℕ, ¬ ChevalleyExceptionalModel (lBar L) .trialityD4 2 n

@[expose] def Item2115 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
      ¬ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

@[expose] def Item2116 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ¬ IsL4L5Sp6 L

@[expose] def Item2117 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ¬ Sec4.IsTripleCover (lBar L) NativeSporadic.M22

@[expose] def Item2118 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, Nonempty (lBar L ≃* SL3 n)) →
      IsIrreducibleOn (wStar A)

@[expose] def Item2119 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n))) →
      IsIrreducibleOn (wStar A)

@[expose] def Item2130 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsIrreducibleOn (wStar A)

theorem rank3II_21_16_of (h212 : Item212) (h2115 : Item2115) : Item2116 :=
  fun G _ _ A E U c L hpair =>
    rank3II_21_16 (h212 G A E U c L hpair) (h2115 G A E U c L hpair)

end CFSG.RankThree.PartTwo.Sec21
