module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

open Subgroup

variable {I : Type*} [Group I]

theorem orderOf_eq_two_of_sq {x : I} (hx2 : x * x = 1) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rwa [pow_two]) hx1

theorem zpow_odd_of_sq {x : I} (hx2 : x * x = 1) {m : ℤ} (hm : Odd m) : x ^ m = x := by
  obtain ⟨j, rfl⟩ := hm
  rw [zpow_add, zpow_mul, show x ^ (2 : ℤ) = 1 from by rw [zpow_two]; exact hx2, one_zpow, one_mul,
    zpow_one]

theorem zpow_even_of_sq {x : I} (hx2 : x * x = 1) {m : ℤ} (hm : Even m) : x ^ m = 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [← two_mul, zpow_mul, show x ^ (2 : ℤ) = 1 from by rw [zpow_two]; exact hx2, one_zpow]

theorem asc_pair_count [Finite I] [DecidableEq I] {t : I} (ht2 : t * t = 1) (htc : ∀ x : I, x * t = t * x)
    (K : Subgroup I) [K.Normal] (hsq : ∀ a : I, a * a ∈ K) (htK : t ∉ K)
    (Zf : Finset I) (hZf : ∀ x, x ∈ Zf ↔ x ∈ K ∧ x * x = 1 ∧ x ≠ 1)
    (hA : ∀ x ∈ Zf, (Zf.filter (fun y => y * x = x * y)).card = 3)
    (hB : ∀ x ∈ Zf, ∀ y ∈ Zf, x * y ≠ y * x → Odd (orderOf (x * y)))
    (Pf : Finset (I × I))
    (hPf : ∀ p, p ∈ Pf ↔ p.1 * p.1 = 1 ∧ p.1 ∉ K ∧ p.2 ∈ Zf ∧ t ∈ zpowers (p.1 * p.2)) :
    Pf.card = Zf.card * (Zf.card - 2) := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htcc : ∀ w : I, t * w = w * t := fun w => (htc w).symm
  set Rf : Finset (I × I) :=
    (Zf ×ˢ Zf).filter (fun p => p.1 = p.2 ∨ p.1 * p.2 ≠ p.2 * p.1) with hRf
  have hbij : Rf.card = Pf.card := by
    refine Finset.card_bij (fun p _ => (t * p.1, p.2)) ?_ ?_ ?_
    · rintro ⟨k, b⟩ hp
      rw [hRf, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hk, hb⟩, hkb⟩ := hp
      simp only at hk hb hkb
      obtain ⟨hkK, hk2, hk1⟩ := (hZf k).1 hk
      rw [hPf]
      refine ⟨?_, ?_, hb, ?_⟩
      · show t * k * (t * k) = 1
        calc t * k * (t * k) = t * (k * t) * k := by group
          _ = t * (t * k) * k := by rw [htc k]
          _ = (t * t) * (k * k) := by group
          _ = 1 := by rw [ht2, hk2, mul_one]
      · intro h
        apply htK
        have : t = (t * k) * k⁻¹ := by group
        rw [this]
        exact K.mul_mem h (K.inv_mem hkK)
      · have hodd : Odd (orderOf (k * b)) := by
          rcases hkb with h | h
          · have : k * b = 1 := by rw [h]; exact (((hZf b).1 hb).2.1)
            rw [this, orderOf_one]; exact odd_one
          · exact hB k hk b hb h
        show t ∈ zpowers (t * k * b)
        have hcw : Commute t (k * b) := htcc (k * b)
        have hw : (t * (k * b)) ^ (orderOf (k * b) : ℤ) = t := by
          rw [hcw.mul_zpow, zpow_odd_of_sq ht2
            (by exact_mod_cast hodd), zpow_natCast, pow_orderOf_eq_one, mul_one]
        exact Subgroup.mem_zpowers_iff.2 ⟨(orderOf (k * b) : ℤ), by rw [mul_assoc]; exact hw⟩
    · rintro ⟨k, b⟩ _ ⟨k', b'⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [mul_left_cancel h1, h2]
    · rintro ⟨a, b⟩ hp
      rw [hPf] at hp
      simp only at hp
      obtain ⟨ha2, haK, hb, hmem⟩ := hp
      obtain ⟨hbK, hb2, hb1⟩ := (hZf b).1 hb
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      let π : I →* I ⧸ K := QuotientGroup.mk' K
      have hπb : π b = 1 := (QuotientGroup.eq_one_iff _).2 hbK
      have hπa2 : π a * π a = 1 := by
        rw [← map_mul]; exact (QuotientGroup.eq_one_iff _).2 (hsq a)
      have hπt : π t ≠ 1 := fun h => htK ((QuotientGroup.eq_one_iff _).1 h)
      have hπm : π t = (π a) ^ m := by
        rw [← hm, map_zpow, map_mul, hπb, mul_one]
      have hmodd : Odd m := by
        by_contra hne
        rw [Int.not_odd_iff_even] at hne
        exact hπt (by rw [hπm]; exact zpow_even_of_sq hπa2 hne)
      have hπa : π t = π a := by rw [hπm]; exact zpow_odd_of_sq hπa2 hmodd
      have hkK : t * a ∈ K := by
        have : π (t * a) = 1 := by rw [map_mul, hπa, hπa2]
        exact (QuotientGroup.eq_one_iff _).1 this
      have hk2 : (t * a) * (t * a) = 1 := by
        calc t * a * (t * a) = t * (a * t) * a := by group
          _ = t * (t * a) * a := by rw [htc a]
          _ = (t * t) * (a * a) := by group
          _ = 1 := by rw [ht2, ha2, mul_one]
      have hak : t * (t * a) = a := by rw [← mul_assoc, ht2, one_mul]
      have hkbm : ((t * a) * b) ^ m = 1 := by
        have h1 : (t * (t * a * b)) ^ m = t := by
          rw [← mul_assoc, hak]; exact hm
        have hcw : Commute t (t * a * b) := htcc _
        rw [hcw.mul_zpow, zpow_odd_of_sq ht2 hmodd] at h1
        exact mul_eq_left.1 h1
      have hk1 : t * a ≠ 1 := by
        intro h
        rw [h, one_mul, zpow_odd_of_sq hb2 hmodd] at hkbm
        exact hb1 hkbm
      have hkZ : t * a ∈ Zf := (hZf _).2 ⟨hkK, hk2, hk1⟩
      have hord : (orderOf ((t * a) * b) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 hkbm
      have hcomm : t * a = b ∨ (t * a) * b ≠ b * (t * a) := by
        by_contra hcon
        push Not at hcon
        obtain ⟨hne, hcomm⟩ := hcon
        have hkb2 : ((t * a) * b) * ((t * a) * b) = 1 := by
          calc (t * a * b) * (t * a * b) = (t * a) * (b * (t * a)) * b := by group
            _ = (t * a) * ((t * a) * b) * b := by rw [← hcomm]
            _ = ((t * a) * (t * a)) * (b * b) := by group
            _ = 1 := by rw [hk2, hb2, mul_one]
        have hkb1 : (t * a) * b ≠ 1 := by
          intro h1
          apply hne
          have : t * a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]
          exact inv_eq_of_mul_eq_one_right hb2
        have h2 := orderOf_eq_two_of_sq hkb2 hkb1
        rw [h2] at hord
        obtain ⟨j, hj⟩ := hord
        exact (Int.not_even_iff_odd.2 hmodd) ⟨j, by omega⟩
      refine ⟨(t * a, b), ?_, ?_⟩
      · rw [hRf, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hkZ, hb⟩, hcomm⟩
      · show (t * (t * a), b) = (a, b)
        rw [hak]
  have hsum : Rf.card = Zf.card * (Zf.card - 2) := by
    rw [hRf, Finset.card_filter, Finset.sum_product_right]
    have hfib : ∀ b ∈ Zf, (∑ k ∈ Zf, if (k = b ∨ k * b ≠ b * k) then 1 else 0) = Zf.card - 2 := by
      intro b hb
      rw [← Finset.card_filter]
      have h3 := hA b hb
      have hsplit := Finset.card_filter_add_card_filter_not (s := Zf)
        (fun k => k = b ∨ k * b ≠ b * k)
      have hnot : Zf.filter (fun k => ¬ (k = b ∨ k * b ≠ b * k)) = (Zf.filter (fun y => y * b = b * y)).erase b := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_erase, not_or, not_not]
        tauto
      rw [hnot, Finset.card_erase_of_mem (by simp [hb]), h3] at hsplit
      omega
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  rw [← hbij, hsum]

end CFSG.Quasithin
