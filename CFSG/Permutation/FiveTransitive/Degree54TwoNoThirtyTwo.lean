module

public import CFSG.Permutation.FiveTransitive.Degree54TwoSmallKernelBound
public import CFSG.Permutation.FiveTransitive.Degree54TwoTwoImages
public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitStructure

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoNoThirtyTwo

open MulAction SylowFixedActionCore

private theorem card_le_two_fifty_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 6)
    (hex : ∃ x : X, Nat.card (orbit Q x) = 16)
    (hsizes : ∀ x : X, Nat.card (orbit Q x) = 1 ∨ Nat.card (orbit Q x) = 2 ∨
      Nat.card (orbit Q x) = 4 ∨ Nat.card (orbit Q x) = 16 ∨ Nat.card (orbit Q x) = 32)
    (himages : ∀ x : X, Nat.card (orbit Q x) = 16 → Nat.card (toPermHom Q (orbit Q x)).range = 16)
    (hno32 : ∀ x : X, Nat.card (orbit Q x) ≠ 32) : Nat.card Q ≤ 256 := by
  obtain ⟨x,hx⟩ := hex
  by_cases hother : ∃ y : X, y ∉ orbit Q x ∧ Nat.card (orbit Q y) = 16
  · obtain ⟨y,hxy,hy⟩ := hother
    have hb := Degree54TwoTwoImages.card_le_product P hcard h5 hnotAlt Q x y hx hy hxy
    rw [himages x hx,himages y hy] at hb
    exact hb
  · have hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 4 := by
      intro y hy
      have hc := hsizes y
      have hn := hno32 y
      have hn16 : Nat.card (orbit Q y) ≠ 16 := fun hh => hother ⟨y,hy,hh⟩
      omega
    have hk := Degree54TwoSmallKernelBound.card_le_eight P hcard h5 hnotAlt Q hQ hQfixed x hx hsmall
    have he := (toPermHom Q (orbit Q x)).ker.card_mul_index
    rw [Subgroup.index_ker,himages x hx] at he
    omega

theorem sylow_card_le_two_fifty_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hno32 : ∀ x : X, Nat.card (orbit (sylowImage X P s S) x) ≠ 32) : Nat.card S ≤ 256 := by
  let Q := sylowImage X P s S
  obtain ⟨⟨x,hx,_⟩,hsizes,himages⟩ := Degree54TwoOrbitStructure.regular_orbit_data P hcard h5 hnotAlt s hs S
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree54TwoEntrance.fixed_six_and_image P hcard h5 hnotAlt s hs S).1
  have hb := card_le_two_fifty_six P hcard h5 hnotAlt Q (S.isPGroup'.map _) hfixed
    ⟨x,hx⟩ hsizes himages hno32
  rwa [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective] at hb

end FiveTransitive.Degree54TwoNoThirtyTwo

end CFSG
