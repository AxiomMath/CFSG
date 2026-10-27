module

public import CFSG.Permutation.FiveTransitive.Degree72ElevenBound
public import CFSG.Permutation.FiveTransitive.Degree72ElevenFixed

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenSylow
open MulAction SylowFixedActionCore

theorem card_le_cube
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) : Nat.card S ≤ 11 ^ 3 := by
  classical
  by_cases hS : Nat.card S = 1
  · rw [hS]; decide
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 11 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective
    (fixingSubgroup P s).subtype_injective
  have hn : Nat.card X < 11 ^ 2 := by rw [Nat.card_eq_fintype_card,hcard]; decide
  let _ : IsMulCommutative Q := Degree72LargePrimeOrbitImage.isMulCommutative 11 (by decide) hQ
    (Degree72LargePrimeOrbitSize.card_le_prime 11 (by decide) hQ hn)
  have hf : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact Degree72ElevenFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  rw [← hQcard]
  exact Degree72ElevenBound.card_le_cube P hcard h5 hnotAlt Q hQ hf

end FiveTransitive.Degree72ElevenSylow

end CFSG
