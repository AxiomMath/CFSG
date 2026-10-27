module

public import CFSG.Permutation.FiveTransitive.Degree79FiveLargeSeven
public import CFSG.Permutation.FiveTransitive.Degree79FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveSharp
open MulAction SylowFixedActionCore

theorem card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S ≤ 5 := by
  classical
  by_cases hS : Nat.card S = 1
  · omega
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hF : Nat.card (fixedPoints Q X) = 9 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree79FiveFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS).1
  obtain ⟨g,hg,hlarge⟩ := Degree79FiveLargeSeven.exists_normalizer_seven P hcard h5 hnotAlt s hs S hS
  have hb := Degree79FiveOrder.card_le_five_of_large_seven_fixed P hcard h5 hnotAlt Q hQ hF g hg hlarge
  have hc : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rwa [hc] at hb

end FiveTransitive.Degree79FiveSharp

end CFSG
