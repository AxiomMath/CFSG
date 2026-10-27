module

public import CFSG.Permutation.FiveTransitive.Degree28TwoGroupReduction
public import CFSG.Permutation.FiveTransitive.Degree28TwoGroupFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree28FiveFixerStructure

open MulAction FixedNormalizerAction

theorem data
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let H := fixingSubgroup P s
    IsPGroup 2 H ∧ 2 ≤ Nat.card H ∧ Nat.card H ≤ 512 ∧
      Nat.card (Fixed (X := X) H) = 6 ∧ Image (X := X) H = ⊤ ∧
      IsMultiplyPretransitive (Normalizer H) (Fixed (X := X) H) 5 := by
  have hH := Degree28TwoGroupReduction.is_two_group P hcard h5 hnotAlt s hs
  obtain ⟨hlo,hhi⟩ := Degree28TwoGroupReduction.card_bounds P hcard h5 hnotAlt s hs
  exact ⟨hH,hlo,hhi,Degree28TwoGroupFixedAction.fixed_card_eq_six P hcard h5 hnotAlt s hs hH,
    Degree28TwoGroupFixedAction.image_eq_top P hcard h5 hnotAlt s hs hH,
    FullFixerFixedAction.normalizer_multiply h5 s hs⟩

end FiveTransitive.Degree28FiveFixerStructure

end CFSG
