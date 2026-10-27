module

public import CFSG.Permutation.FiveTransitive.FullFixerSharpFive
public import CFSG.Permutation.FiveTransitive.Degree28TwoGroupTwelveExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree28TwoGroupFixedAction

open MulAction FixedNormalizerAction

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : IsPGroup 2 (fixingSubgroup P s)) :
    Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 6 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcases := FullFixerSharpFive.fixed_degree_cases h5 s hs
  have hpar := hH.card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints (fixingSubgroup P s) X) % 2 at hpar
  rw [Nat.card_eq_fintype_card,hcard,← fixed_eq] at hpar
  have hnot12 : Nat.card (Fixed (X := X) (fixingSubgroup P s)) ≠ 12 := by
    intro h12
    exact Degree28TwoGroupTwelveExclusion.false_of_five_transitive P hcard h5 hnotAlt
      (fixingSubgroup P s) hH h12 (FullFixerFixedAction.normalizer_multiply h5 s hs)
  dsimp only at hcases
  omega

theorem image_eq_top
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : IsPGroup 2 (fixingSubgroup P s)) :
    Image (X := X) (fixingSubgroup P s) = ⊤ := by
  have hsix := fixed_card_eq_six P hcard h5 hnotAlt s hs hH
  have hsharp := (FullFixerSharpFive.sharp_image h5 s hs).2.2
  apply Subgroup.eq_top_of_card_eq
  rw [hsharp,Nat.card_perm,hsix]
  norm_num [Nat.factorial,Nat.descFactorial]

end FiveTransitive.Degree28TwoGroupFixedAction

end CFSG
