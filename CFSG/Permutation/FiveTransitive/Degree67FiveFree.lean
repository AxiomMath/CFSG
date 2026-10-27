module

public import CFSG.Permutation.FiveTransitive.Degree67FiveFreeCore
public import CFSG.Permutation.FiveTransitive.Degree67ThreeFree

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveFree

open MulAction

theorem three_fixed_card_le_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 3) : Nat.card (Function.fixedPoints g.val) ≤ 4 := by
  by_contra hn
  have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
  let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = 3 := (Subgroup.orderOf_coe u).symm.trans hg
  exact Degree67ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
    (hu ▸ orderOf_dvd_natCard u)

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree67FiveFreeCore.not_dvd_five_fixer P hcard h5 hnotAlt
    (Degree67SevenFree.fixed_card_eq_four P hcard h5 hnotAlt)
    (three_fixed_card_le_four P hcard h5 hnotAlt) s hs

theorem fixed_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 2 := by
  exact Degree67FiveFreeCore.fixed_card_eq_two P hcard h5 hnotAlt
    (Degree67SevenFree.fixed_card_eq_four P hcard h5 hnotAlt)
    (three_fixed_card_le_four P hcard h5 hnotAlt) g hg

end FiveTransitive.Degree67FiveFree

end CFSG
