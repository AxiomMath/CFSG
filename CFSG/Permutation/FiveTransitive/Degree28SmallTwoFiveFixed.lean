module

public import CFSG.Permutation.FiveTransitive.Degree28FiveSevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree28SmallTwoFiveFixed

open MulAction

theorem global_fixed_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (z : P) (hz : orderOf z = 5) : Nat.card (Function.fixedPoints z.val) = 3 := by
  have hle : Nat.card (Function.fixedPoints z.val) ≤ 4 := by
    by_contra hn
    have hfive : 5 ≤ (Function.fixedPoints z.val).ncard := by
      rw [← Nat.card_coe_set_eq]
      omega
    obtain ⟨s,hs,hsc⟩ := Set.exists_subset_card_eq hfive
    have hzmem : z ∈ fixingSubgroup P s := by
      apply (mem_fixingSubgroup_iff P).mpr
      intro x hx
      exact hs hx
    have horder : orderOf (⟨z,hzmem⟩ : fixingSubgroup P s) = 5 := by
      rw [← Subgroup.orderOf_coe,hz]
    exact (Degree28FiveSevenFree.five_and_seven_not_dvd_five_fixer_card P hcard h5 hnotAlt s hsc).1
      (horder ▸ orderOf_dvd_natCard (⟨z,hzmem⟩ : fixingSubgroup P s))
  obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val) (by
    rw [Subgroup.orderOf_coe,hz]; norm_num)
  have hsum := z.val.sum_cycleType
  rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,Subgroup.orderOf_coe,hz] at hsum
  have hbound := Finset.card_le_univ z.val.support
  rw [hcard] at hbound
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.sum_cycleType,hcard] at hle ⊢
  omega

theorem local_fixed_eq_one
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (hcard : Fintype.card Y = 6) (z : Equiv.Perm Y) (hz : orderOf z = 5) :
    Nat.card (Function.fixedPoints z) = 1 := by
  obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := z) (by rw [hz]; norm_num)
  have hsum := z.sum_cycleType
  rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hz] at hsum
  have hbound := Finset.card_le_univ z.support
  rw [hcard] at hbound
  have hpos : z.support.card ≠ 0 := by
    intro hh
    have he : z = 1 := Equiv.Perm.card_support_eq_zero.mp hh
    rw [he,orderOf_one] at hz
    omega
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree28SmallTwoFiveFixed

end CFSG
