module

public import CFSG.Permutation.FiveTransitive.Degree60ElevenDescentOrderCore

public section

namespace CFSG

namespace FiveTransitive.Degree60ElevenDescentOrder

open MulAction Subgroup SylowFixedActionCore

theorem sylow_card_le_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) : Nat.card S ≤ 11 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_cases hS : Nat.card S = 1
  · omega
  let Q := sylowImage X P s S
  have hQ : IsPGroup 11 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hF : Nat.card (fixedPoints Q X) = 5 := by
    rw [← hfixeq]
    exact (Degree60ElevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hb := Degree60ElevenDescentOrderCore.card_le_eleven P hcard h5 hnotAlt
    Q hQ hF
  have heq : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rwa [heq] at hb

end FiveTransitive.Degree60ElevenDescentOrder

end CFSG
