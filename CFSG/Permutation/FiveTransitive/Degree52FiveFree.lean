module

public import CFSG.Permutation.FiveTransitive.Degree52FiveFreeCore
public import CFSG.Permutation.FiveTransitive.Degree52SevenFree
public import CFSG.Permutation.FiveTransitive.Degree52SylowFiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree52FiveFree

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree52FiveFreeCore.not_dvd_five_fixer_of_seven_fixed_three P hcard h5 hnotAlt
    (Degree52SevenFree.fixed_card_eq_three P hcard h5 hnotAlt) s hs

theorem fixed_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 2 := by
  classical
  rcases Degree52SylowFiveOrder.fixed_card_two_or_seven P hcard h5 hnotAlt g hg with h | h
  · exact h
  · have hn : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq,h]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hn
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
    exact False.elim (not_dvd_five_fixer P hcard h5 hnotAlt s hs (hu ▸ orderOf_dvd_natCard u))

end FiveTransitive.Degree52FiveFree

end CFSG
