module

public import CFSG.Permutation.FiveTransitive.OrderNineFixedCount
public import CFSG.Permutation.FiveTransitive.ExponentThreeInversePairs

public section

namespace CFSG

namespace FiveTransitive.OrderNineTwoFixedCounts
open MulAction
open scoped BigOperators

private theorem constraints
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hH : Nat.card H = 9) (hpow : ∀ h : H, h ^ 3 = 1) (a : ℕ)
    (hcases : ∀ h : H, h ≠ 1 → Nat.card (fixedBy Y h) = a ∨
      Nat.card (fixedBy Y h) = a + 3) :
    let k := {h : H | h ≠ 1 ∧ Nat.card (fixedBy Y h) = a + 3}.ncard
    Even k ∧ k ≤ 8 ∧ 9 ∣ Nat.card Y + 8 * a + 3 * k := by
  classical
  let _ : Fintype H := Fintype.ofFinite _
  let _ : Fintype Y := Fintype.ofFinite _
  let T : Set H := {h : H | h ≠ 1 ∧ Nat.card (fixedBy Y h) = a + 3}
  let t : Finset H := T.toFinset
  let s : Finset H := Finset.univ.erase 1
  have hs : s.card = 8 := by
    simp only [s,Finset.card_erase_of_mem (Finset.mem_univ (1:H)),Finset.card_univ,
      ← Nat.card_eq_fintype_card,hH]
  have hts : t ⊆ s := by
    intro h hh
    exact Finset.mem_erase.mpr ⟨(Set.mem_toFinset.mp hh).1,Finset.mem_univ _⟩
  have ht : t.card = T.ncard := (Set.ncard_eq_toFinset_card' T).symm
  have heven : Even T.ncard := ExponentThreeInversePairs.even_ncard hpow T
    (fun h => h.1 rfl) (by
      intro h hh
      exact ⟨inv_ne_one.mpr hh.1,by simpa only [fixedBy_inv] using hh.2⟩)
  have hpoint : ∀ h ∈ s, Nat.card (fixedBy Y h) = a + if h ∈ t then 3 else 0 := by
    intro h hh
    have hn := (Finset.mem_erase.mp hh).1
    by_cases hm : h ∈ t
    · simp only [hm,ite_true]
      exact (Set.mem_toFinset.mp hm).2
    · simp only [hm,ite_false,add_zero]
      rcases hcases h hn with he | he
      · exact he
      · exact (hm (Set.mem_toFinset.mpr ⟨hn,he⟩)).elim
  have he : (∑ h ∈ s, Nat.card (fixedBy Y h)) = 8 * a + 3 * T.ncard := by
    rw [Finset.sum_congr rfl hpoint,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hs]
    have hfilter : s.filter (fun h => h ∈ t) = t := by
      ext h
      simp only [Finset.mem_filter]
      exact ⟨fun hh => hh.2,fun hh => ⟨hts hh,hh⟩⟩
    rw [← Finset.sum_filter,hfilter,Finset.sum_const,nsmul_eq_mul,ht]
    simp only [Nat.cast_id,Nat.mul_comm]
  have hd := OrderNineFixedCount.nine_dvd_sum (Y := Y) hH
  have hone : Nat.card (fixedBy Y (1 : H)) = Nat.card Y := by
    rw [fixedBy_one_eq_univ,Nat.card_coe_set_eq,Set.ncard_univ]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1:H)),hone] at hd
  change 9 ∣ (∑ h ∈ s, Nat.card (fixedBy Y h)) + Nat.card Y at hd
  rw [he] at hd
  change Even T.ncard ∧ T.ncard ≤ 8 ∧ _
  refine ⟨heven,?_,?_⟩
  · rw [← ht,← hs]
    exact Finset.card_le_card hts
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hd

theorem local_count_four
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hH : Nat.card H = 9) (hpow : ∀ h : H, h ^ 3 = 1)
    (hY : Nat.card Y = 6)
    (hcases : ∀ h : H, h ≠ 1 → Nat.card (fixedBy Y h) = 0 ∨
      Nat.card (fixedBy Y h) = 3) :
    {h : H | h ≠ 1 ∧ Nat.card (fixedBy Y h) = 3}.ncard = 4 := by
  have hk := constraints hH hpow 0 hcases
  simp only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] at hk
  obtain ⟨he,hb,hd⟩ := hk
  rw [hY] at hd
  obtain ⟨j,hj⟩ := he
  have hm := Nat.mod_eq_zero_of_dvd hd
  omega

theorem global_count_four
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hH : Nat.card H = 9) (hpow : ∀ h : H, h ^ 3 = 1)
    (hY : Nat.card Y = 80)
    (hcases : ∀ h : H, h ≠ 1 → Nat.card (fixedBy Y h) = 2 ∨
      Nat.card (fixedBy Y h) = 5) :
    {h : H | h ≠ 1 ∧ Nat.card (fixedBy Y h) = 5}.ncard = 4 := by
  have hk := constraints hH hpow 2 hcases
  simp only [Nat.reduceAdd] at hk
  obtain ⟨he,hb,hd⟩ := hk
  rw [hY] at hd
  obtain ⟨j,hj⟩ := he
  have hm := Nat.mod_eq_zero_of_dvd hd
  omega

end FiveTransitive.OrderNineTwoFixedCounts

end CFSG
