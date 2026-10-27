module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG

namespace FiveTransitive.OrderNineFixedCount
open MulAction
open scoped BigOperators

theorem nine_dvd_sum
    {H Y : Type*} [Group H] [Fintype H] [Fintype Y] [MulAction H Y]
    (hH : Nat.card H = 9) : 9 ∣ ∑ h : H, Nat.card (fixedBy Y h) := by
  classical
  let _ : Fintype (Quotient (orbitRel H Y)) := Fintype.ofFinite _
  have he := sum_card_fixedBy_eq_card_orbits_mul_card_group H Y
  simp only [← Nat.card_eq_fintype_card,hH] at he
  rw [he]
  exact dvd_mul_left _ _

theorem constant_divisibility
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hH : Nat.card H = 9) (t : ℕ)
    (ht : ∀ h : H, h ≠ 1 → Nat.card (fixedBy Y h) = t) :
    9 ∣ Nat.card Y + 8 * t := by
  classical
  let _ : Fintype H := Fintype.ofFinite _
  let _ : Fintype Y := Fintype.ofFinite _
  have hd := nine_dvd_sum (Y := Y) hH
  have hone : Nat.card (fixedBy Y (1 : H)) = Nat.card Y := by
    rw [fixedBy_one_eq_univ,Nat.card_coe_set_eq,Set.ncard_univ]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : H)),hone] at hd
  have he : (∑ h ∈ (Finset.univ : Finset H).erase 1, Nat.card (fixedBy Y h)) = 8 * t := by
    rw [Finset.sum_congr rfl (fun h hh => ht h (Finset.mem_erase.mp hh).1)]
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ (1:H)),
      Finset.card_univ,← Nat.card_eq_fintype_card,hH,Nat.cast_id]
  rw [he] at hd
  simpa only [Nat.add_comm] using hd

theorem constant_congruence
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hH : Nat.card H = 9) (t : ℕ)
    (ht : ∀ h : H, h ≠ 1 → Nat.card (fixedBy Y h) = t) :
    Nat.card Y % 9 = t % 9 := by
  have hd := constant_divisibility hH t ht
  have hm := Nat.mod_eq_zero_of_dvd hd
  omega

end FiveTransitive.OrderNineFixedCount

end CFSG
