module

public import CFSG.Permutation.FiveTransitive.SimpleActionEven
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG

namespace FiveTransitive.NineAlternatingDoubleImageGeometry

private theorem cycleType_eq_two_swaps
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (u : Equiv.Perm F) (hu : u ^ 2 = 1)
    (hfix : Nat.card (Function.fixedPoints u) = 5) : u.cycleType = {2, 2} := by
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hu
  have hc := u.card_fixedPoints
  rw [← Nat.card_eq_fintype_card, hfix, ← Nat.card_eq_fintype_card, hF,
    ht, Multiset.sum_replicate, nsmul_eq_mul] at hc
  have hb := u.sum_cycleType_le
  rw [ht, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hF] at hb
  simp only [Nat.cast_id] at hc hb
  have hm : u.cycleType.card = 2 := by omega
  rw [ht, hm]
  rfl

theorem exists_commuting_five
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (u : Equiv.Perm F) (hu : u ^ 2 = 1)
    (hfix : Nat.card (Function.fixedPoints u) = 5) :
    ∃ v : alternatingGroup F, orderOf v = 5 ∧ Commute u v.val := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let C := Subgroup.centralizer ({u} : Set (Equiv.Perm F))
  have hC : Nat.card C = 960 := by
    rw [Equiv.Perm.nat_card_centralizer, cycleType_eq_two_swaps hF u hu hfix,
      ← Nat.card_eq_fintype_card, hF]
    norm_num [Nat.factorial]
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 (by rw [hC]; norm_num)
  have hv5 : v.val ^ 5 = 1 := by
    exact congrArg Subtype.val (hv ▸ pow_orderOf_eq_one v)
  have hsign : v.val.sign = 1 := by
    have hs := congrArg Equiv.Perm.sign hv5
    rw [map_pow, map_one] at hs
    rcases Int.units_eq_one_or v.val.sign with h | h
    · exact h
    · rw [h] at hs
      exact False.elim ((by decide : (-1 : ℤˣ) ^ 5 ≠ 1) hs)
  let w : alternatingGroup F := ⟨v.val, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  refine ⟨w, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe w]
    exact (Subgroup.orderOf_coe v).trans hv
  · exact (Subgroup.mem_centralizer_singleton_iff.mp v.property).symm

theorem fixed_five_of_centralizer_five_dvd
    {E : Type*} [Fintype E] [DecidableEq E] (hE : Nat.card E = 9)
    (p : Equiv.Perm E) (hp : p ^ 2 = 1) (hne : p ≠ 1) (hsign : p.sign = 1)
    (hfive : 5 ∣ Nat.card (Subgroup.centralizer ({p} : Set (Equiv.Perm E)))) :
    Nat.card (Function.fixedPoints p) = 5 := by
  have hd := SimpleActionEven.four_dvd_support_of_even_involution p hp hsign
  have hb := Finset.card_le_univ p.support
  rw [← Nat.card_eq_fintype_card, hE] at hb
  have hpos : 0 < p.support.card := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hne (Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp hz))
  have hcases : p.support.card = 4 ∨ p.support.card = 8 := by omega
  rcases hcases with hfour | height
  · rw [Nat.card_eq_fintype_card, p.card_fixedPoints, p.sum_cycleType, hfour,
      ← Nat.card_eq_fintype_card, hE]
  · exfalso
    have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
    have hsum := p.sum_cycleType
    rw [ht, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, height] at hsum
    have hm : p.cycleType.card = 4 := by omega
    have hC : Nat.card (Subgroup.centralizer ({p} : Set (Equiv.Perm E))) = 384 := by
      rw [Equiv.Perm.nat_card_centralizer, ht, hm, ← Nat.card_eq_fintype_card, hE]
      norm_num [Nat.factorial]
    rw [hC] at hfive
    norm_num at hfive

end FiveTransitive.NineAlternatingDoubleImageGeometry

end CFSG
