module

public import CFSG.Permutation.FiveTransitive.Degree18Burnside

public section

namespace CFSG

namespace FiveTransitive.Degree18

open MulAction SubMulAction Subgroup

theorem classification_of_five_transitive_of_card_eq_eighteen
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X :=
    MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X,
        Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    intro i
    exact hg i
  have hAlt : alternatingGroup X ≤ P :=
    alternatingGroup_le_of_five_transitive_of_card_eq_eighteen
      X P hcard h5P
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree18

end CFSG
