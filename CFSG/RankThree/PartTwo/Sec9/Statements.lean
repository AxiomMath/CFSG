module

public import CFSG.RankThree.PartTwo.Sec9.Notation
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Item93 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G) (n : ℕ), Hyp92 G A c L a R n → 1 < n

@[expose] def Hyp92Never : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G) (n : ℕ), ¬ Hyp92 G A c L a R n

@[expose] def IsList1016 (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧
      Nonempty (X ≃* projSL 2 (GaloisField p (3 * e)))) ∨
    (∃ n : ℕ, 1 < n ∧ Nonempty (X ≃* projSL 2 (GaloisField 2 (3 * n)))) ∨
    ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)

@[expose] def Item96 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Hyp91 G A c L a R →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∨
        IsList1016 (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def NotLTwoEight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Hyp91 G A c L a R →
      ¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 3))

@[expose] def Item97 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Hyp91 G A c L a R →
      Nat.card (A ⊓ L : Subgroup G) = 3 ∧
        ∀ d : G, A ⊓ L = Subgroup.zpowers d → A = Subgroup.closure {c, a, d}

@[expose] def Item98 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Hyp91 G A c L a R →
      ∃ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ A ∧
        (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≠ Subgroup.zpowers c

theorem item96_of_item82
    (h82 : Sec8.Item82One) (h92 : Hyp92Never) (h8 : NotLTwoEight) : Item96 := by
  intro G _ _ A c L a R h
  rcases h82 G A c L a h.toHyp81 h.card_eq with h27 | hp | ⟨m, hm, h2 | h3 | h4⟩
  · exact Or.inl h27
  · exact Or.inr (Or.inl hp)
  · rcases Nat.lt_or_ge 1 m with hm1 | hm1
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm1, h2⟩))
    · obtain rfl : m = 1 := le_antisymm hm1 hm
      exact absurd h2 (h8 G A c L a R h)
  · exact Or.inr (Or.inr (Or.inr ⟨m, hm, h3⟩))
  · exact absurd ⟨h, h4⟩ (h92 G A c L a R m)

end CFSG.RankThree.PartTwo.Sec9
