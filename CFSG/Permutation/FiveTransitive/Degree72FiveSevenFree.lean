module

public import CFSG.Permutation.FiveTransitive.Degree72SevenFiveFixed
public import CFSG.Permutation.FiveTransitive.Degree72FiveGlobal

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveSevenFree

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  apply Degree72SevenFiveFixed.not_dvd_five_fixer_of_five_fixed_le P hcard h5 hnotAlt _ s hs
  intro g hg
  exact (Degree72FiveGlobal.fixed_card_le_twelve P hcard h5 hnotAlt g hg).trans (by decide)

theorem fixed_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 7) : Nat.card (Function.fixedPoints g.val) = 2 := by
  classical
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hf : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [←Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hf
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 7 := (Subgroup.orderOf_coe u).symm.trans hg
    exact not_dvd_five_fixer P hcard h5 hnotAlt s hs (hu ▸ orderOf_dvd_natCard u)
  have hgperm : orderOf g.val = 7 := (Subgroup.orderOf_coe g).trans hg
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order (σ := g.val) (by rw [hgperm]; norm_num)
  have hsum := g.val.sum_cycleType
  rw [hm,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hgperm] at hsum
  have hle : g.val.support.card ≤ 72 := hcard ▸ Finset.card_le_univ g.val.support
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.sum_cycleType,hcard] at hlt ⊢
  omega

end FiveTransitive.Degree72FiveSevenFree

end CFSG
