module

public import CFSG.Permutation.FiveTransitive.Degree60FiveOrderCore
public import CFSG.Permutation.FiveTransitive.Degree60SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveOrder

open MulAction Subgroup SylowFixedActionCore

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) :
    Nat.card (Function.fixedPoints g.val) = 0 ∨ Nat.card (Function.fixedPoints g.val) = 5 := by
  exact Degree60FiveOrderCore.fixed_card_cases P hcard h5 hnotAlt
    (Degree60SevenFree.fixed_card_eq_four P hcard h5 hnotAlt) g hg

theorem sylow_card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_cases hS : Nat.card S = 1
  · omega
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hF : Nat.card (fixedPoints Q X) = 5 := by
    rw [← hfixeq]
    exact (Degree60FiveFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hb := Degree60FiveOrderCore.card_le_five P hcard h5 hnotAlt
    (Degree60SevenFree.fixed_card_eq_four P hcard h5 hnotAlt) Q hQ hF
  have heq : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rwa [heq] at hb

end FiveTransitive.Degree60FiveOrder

end CFSG
