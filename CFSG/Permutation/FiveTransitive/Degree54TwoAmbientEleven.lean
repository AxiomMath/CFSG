module

public import CFSG.Permutation.FiveTransitive.Degree54LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoAmbientEleven

open MulAction

theorem eleven_not_dvd_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 11 ∣ Nat.card P := by
  classical
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ, hcard])
  have ht : IsMultiplyPretransitive P X s.ncard := by rw [hs]; exact h5
  have hi := ht.index_of_fixingSubgroup_eq s
  have hind : ¬ 11 ∣ (fixingSubgroup P s).index := by
    rw [hi, Nat.card_eq_fintype_card, hcard, hs]
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  have hfix := Degree54LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
    11 (by decide) (by omega)
  rw [← (fixingSubgroup P s).index_mul_card]
  exact (show Nat.Prime 11 by decide).not_dvd_mul hind hfix

end FiveTransitive.Degree54TwoAmbientEleven

end CFSG
