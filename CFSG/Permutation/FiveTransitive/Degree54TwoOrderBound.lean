module

public import CFSG.Permutation.FiveTransitive.Degree54TwoNoThirtyTwo
public import CFSG.Permutation.FiveTransitive.Degree54ThirtyTwoKernel

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoOrderBound

open MulAction SylowFixedActionCore

theorem sylow_card_le_five_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S ≤ 512 := by
  classical
  let Q := sylowImage X P s S
  by_cases h32 : ∃ y : X, Nat.card (orbit Q y) = 32
  · obtain ⟨y,hy⟩ := h32
    obtain ⟨⟨x,hx,himage⟩,_,_⟩ := Degree54TwoOrbitStructure.regular_orbit_data P hcard h5 hnotAlt s hs S
    have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
    have hQfixed : Nat.card (fixedPoints Q X) = 6 := by
      rw [← FixedNormalizerAction.fixed_eq Q]
      exact (Degree54TwoEntrance.fixed_six_and_image P hcard h5 hnotAlt s hs S).1
    obtain ⟨g,hg,_,hfixed⟩ := Degree54TwoOrbitFiveLift.exists_five_three_exterior P hcard h5 hnotAlt s hs S
    have hk := Degree54ThirtyTwoKernel.card_le_thirty_two P hcard h5 hnotAlt Q hQ hQfixed
      g (hg ▸ pow_orderOf_eq_one g) hfixed x y hx hy
    have he := (toPermHom Q (orbit Q x)).ker.card_mul_index
    rw [Subgroup.index_ker,himage] at he
    have hb : Nat.card Q ≤ 512 := by omega
    rwa [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective] at hb
  · have hno : ∀ y : X, Nat.card (orbit Q y) ≠ 32 := by
      intro y hy
      exact h32 ⟨y,hy⟩
    exact (Degree54TwoNoThirtyTwo.sylow_card_le_two_fifty_six P hcard h5 hnotAlt s hs S hno).trans (by decide)

end FiveTransitive.Degree54TwoOrderBound

end CFSG
