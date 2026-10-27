module

public import CFSG.RankThree.PartOne.Q1327T.Defs

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327T

@[expose] def Row8OddConcl (p : ℕ) (Q : Type) [Group Q] (Ē : Subgroup Q) : Prop :=
  ¬ p ∣ Nat.card ↥(torusImage Ē ⊤) → OddOrderOneOrThree ↥(torusImage Ē ⊤)

@[expose] def Row8OddAt (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (p g : ℕ) (Ē : Subgroup Q), 11 ≤ p →
    Subgroup.center Q = ⊥ → P (Q ⧸ Subgroup.center Q) → Row8Conf p g Q Ē → Row8OddConcl p Q Ē

theorem Row8OddAt.of_exists {ι : Type} {P : (X : Type) → [Group X] → Prop}
    {Q : ι → (X : Type) → [Group X] → Prop}
    (hcov : ∀ (X : Type) [Group X], P X → ∃ i, Q i X) (h : ∀ i, Row8OddAt (Q i)) :
    Row8OddAt P := fun T _ _ p g Ē hp hZ hP hc => by
  obtain ⟨i, hi⟩ := hcov _ hP
  exact h i T p g Ē hp hZ hi hc

@[expose] def Row8OddInspection : Prop := Row8OddAt fun _ _ => True

@[expose] def Row8OddItem (i : Fin 9) : Prop := Row8OddAt (thmThreeItem i)

theorem row8Odd_of_items (h : ∀ i : Fin 9, Row8OddItem i) : Row8OddInspection := by
  intro T _ _ p g Ē hp hZ _ hc
  have hl := hc.onList
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact h 0 T p g Ē hp hZ h1 hc
  · exact h 1 T p g Ē hp hZ h2 hc
  · exact h 2 T p g Ē hp hZ h3 hc
  · exact h 3 T p g Ē hp hZ h4 hc
  · exact h 4 T p g Ē hp hZ h5 hc
  · exact h 5 T p g Ē hp hZ h6 hc
  · exact h 6 T p g Ē hp hZ h7 hc
  · exact h 7 T p g Ē hp hZ h8 hc
  · exact h 8 T p g Ē hp hZ h9 hc

end CFSG.RankThree.PartOne.K133B
