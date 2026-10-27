module

public import CFSG.RankThree.PartTwo.Sec15.Item15Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def KS1521SylAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 1 ≤ m → Sec4.IsoLThreePi X 2 m →
    ∀ p : ℕ, IsChoice1519 m p → 3 < p →
      (∀ S : Subgroup X, IsPGroup p S → IsMulCommutative S) ∧
      ∀ (φ : MulAut X) (k : ℕ), φ ^ p ^ k = 1 → ∃ x : X, φ = MulAut.conj x

structure Ext1521 (A P X T : Subgroup G) : Prop where
  mem_y2 : X ∈ scriptY2 A
  le_x : P ≤ X
  mem_t : T ∈ scriptQPi A (lB A) X (piOf 2)
  card_le : ∀ X' ∈ scriptY2 A, P ≤ X' → ∀ T' ∈ scriptQPi A (lB A) X' (piOf 2),
    Nat.card T' ≤ Nat.card T
  normalizer_le : Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ X

end CFSG.RankThree.PartTwo.Sec15
