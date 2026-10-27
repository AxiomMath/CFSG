module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec11.Item116R1RankTwoPure

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def ThreeCoverModelA (Q : Type) [Group Q] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi Q p e) ∨
    Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨ Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (Q ≃* Blueprint.NativeSporadic.M22) ∨ Nonempty (Q ≃* Blueprint.NativeSporadic.ON)

@[expose] def ThreeCoverModelB (Q : Type) [Group Q] : Prop :=
  Blueprint.ChevalleyExceptionalModel Q .G2 3 1 ∨ Nonempty (Q ≃* projSU 4 3 1) ∨
    Nonempty (Q ≃* Blueprint.NativeSporadic.J3) ∨ Nonempty (Q ≃* Blueprint.NativeSporadic.McL)

@[expose] def SylowThreeNotRankTwoByCyclic : Prop :=
  ∀ (P : Type) [Group P] [Finite P], ThreeCoverModelB P →
    ∀ T : Sylow 3 P, ¬ IsRankTwoByCyclic ↥(T : Subgroup P)

theorem item4_3_split {Q : Type} [Group Q]
    (h : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi Q p e) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
      Blueprint.ChevalleyExceptionalModel Q .G2 3 1 ∨
      Nonempty (Q ≃* projSU 4 3 1) ∨
      Nonempty (Q ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (Q ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (Q ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (Q ≃* Blueprint.NativeSporadic.ON)) :
    ThreeCoverModelA Q ∨ ThreeCoverModelB Q := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))

end CFSG.RankThree.PartTwo.Sec11
