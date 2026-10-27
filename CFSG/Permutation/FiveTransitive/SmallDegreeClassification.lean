module

public import CFSG.Permutation.FiveTransitive.Degree16Classification
public import CFSG.Permutation.FiveTransitive.Degree17
public import CFSG.Permutation.FiveTransitive.Degree18
public import CFSG.Permutation.FiveTransitive.Degree19
public import CFSG.Permutation.FiveTransitive.Degree20ThreePointStabilizer
public import CFSG.Permutation.FiveTransitive.Degree21_23_27
public import CFSG.Permutation.FiveTransitive.Degree22Classification
public import CFSG.Permutation.FiveTransitive.Degree24Classification
public import CFSG.Permutation.FiveTransitive.Degree25Classification
public import CFSG.Permutation.FiveTransitive.Degree26

public section

namespace CFSG

namespace FiveTransitive.SmallDegreeClassification

theorem subgroup_card_classification
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hlower : 5 ≤ Fintype.card X)
    (hupper : Fintype.card X ≤ 27)
    (h5 : MulAction.IsMultiplyPretransitive P X 5) :
    Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Nat.card P = (Fintype.card X).factorial / 2) ∨
      (Fintype.card X = 12 ∧ Nat.card P = 95040) ∨
      (Fintype.card X = 24 ∧ Nat.card P = 244823040) := by
  classical
  letI : Fintype P := Fintype.ofFinite _
  have h5explicit :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    rw [MulAction.isMultiplyPretransitive_iff] at h5
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨g, ?_⟩
    intro i
    have hi := congrArg (fun e : Fin 5 ↪ X => e i) hg
    simpa [Function.Embedding.smul_apply] using hi
  have hcases :
      Fintype.card X ≤ 11 ∨
      Fintype.card X = 12 ∨ Fintype.card X = 13 ∨
      Fintype.card X = 14 ∨ Fintype.card X = 15 ∨
      Fintype.card X = 16 ∨ Fintype.card X = 17 ∨
      Fintype.card X = 18 ∨ Fintype.card X = 19 ∨
      Fintype.card X = 20 ∨ Fintype.card X = 21 ∨
      Fintype.card X = 22 ∨ Fintype.card X = 23 ∨
      Fintype.card X = 24 ∨ Fintype.card X = 25 ∨
      Fintype.card X = 26 ∨ Fintype.card X = 27 := by
    omega
  rcases hcases with hle11 | h12 | h13 | h14 | h15 | h16 | h17 |
      h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27
  · rcases FiveTransitive.Helpers.classification_of_five_transitive_of_card_le_eleven
        P X hlower hle11 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Helpers.classification_of_five_transitive_of_card_eq_twelve
        P X h12 h5explicit with hSym | hAlt | hM12
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
    · exact Or.inr (Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hM12)))
  · rcases FiveTransitive.Helpers.classification_of_five_transitive_of_card_eq_thirteen
        P X h13 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree14.classification_of_five_transitive_of_card_eq_fourteen
        P X h14 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree15.classification_of_five_transitive_of_card_eq_fifteen
        P X h15 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree16.classification_of_five_transitive_of_card_eq_sixteen
        P X h16 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree17.classification_of_five_transitive_of_card_eq_seventeen
        P X h17 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree18.classification_of_five_transitive_of_card_eq_eighteen
        P X h18 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree19.classification_of_five_transitive_of_card_eq_nineteen
        P X h19 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree20.classification_of_five_transitive_of_card_eq_twenty
        P X h20 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree21_23_27.classification_of_five_transitive_of_card_eq_twentyOne
        P X h21 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree22.classification_of_five_transitive_of_card_eq_twentyTwo
        P X h22 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree21_23_27.classification_of_five_transitive_of_card_eq_twentyThree
        P X h23 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree24.card_classification_of_five_transitive
        P X h24 h5explicit with hSym | hAlt | hM24
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
    · exact Or.inr (Or.inr (Or.inr (by
        simpa only [Nat.card_eq_fintype_card] using hM24)))
  · rcases FiveTransitive.Degree25.classification_of_five_transitive_of_card_eq_twentyFive
        P X h25 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree26.classification_of_five_transitive_of_card_eq_twentySix
        P X h26 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))
  · rcases FiveTransitive.Degree21_23_27.classification_of_five_transitive_of_card_eq_twentySeven
        P X h27 h5explicit with hSym | hAlt
    · exact Or.inl (by simpa only [Nat.card_eq_fintype_card] using hSym)
    · exact Or.inr (Or.inl (by
        simpa only [Nat.card_eq_fintype_card] using hAlt))

end FiveTransitive.SmallDegreeClassification

end CFSG
