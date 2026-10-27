module

public import CFSG.Permutation.FiveTransitive.Degree24ReducedCases
public import CFSG.Permutation.FiveTransitive.Degree24Order96Final

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem card_classification_of_five_transitive
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) ∨
      (Fintype.card X = 24 ∧ Fintype.card G = 244823040) := by
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
  by_cases hAlt : alternatingGroup X ≤ P
  · rcases
      FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
        G X (by omega) hAlt with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hP5 :
        MulAction.IsMultiplyPretransitive P X 5 := by
      rw [MulAction.isMultiplyPretransitive_iff]
      intro a b
      obtain ⟨g, hg⟩ :=
        h5P a b a.injective b.injective
      refine ⟨g, ?_⟩
      ext i
      exact hg i
    obtain ⟨s, _, hs⟩ :=
      Set.exists_subset_card_eq
        (s := (Set.univ : Set X)) (n := 5) (by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card,
            hcard]
          norm_num)
    let H : Subgroup P := fixingSubgroup P s
    have hcases :
        Nat.card H = 48 ∨ Nat.card H = 96 ∨ False := by
      simpa only [H] using
        five_point_stabilizer_card_reduced_cases
          X P hcard h5P hAlt s hs
    have hHindexRaw :=
      hP5.index_of_fixingSubgroup_mul hs
    rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
    norm_num at hHindexRaw
    have hHindex : H.index = 5100480 := by
      change (fixingSubgroup P s).index = 5100480
      omega
    have hHindexCard := H.index_mul_card
    have hcardRange :
        Fintype.card G = Nat.card P := by
      rw [Nat.card_eq_fintype_card]
      exact
        Fintype.card_congr
          (Equiv.ofInjective φ MulAction.toPerm_injective)
    rcases hcases with hHcard | hHcard | hfalse
    · right
      right
      refine ⟨hcard, ?_⟩
      rw [hcardRange]
      rw [hHindex, hHcard] at hHindexCard
      omega
    · exact False.elim
        ((five_point_stabilizer_card_ne_ninety_six
          X P hcard h5P hAlt s hs) hHcard)
    · exact hfalse.elim

end FiveTransitive.Degree24

end CFSG
