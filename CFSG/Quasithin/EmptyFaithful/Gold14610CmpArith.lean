module

public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpTwo
public import Mathlib.Data.Finset.Image
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Prime.Basic

public section

namespace CFSG.Quasithin.Gold14610

@[expose] def F618S : Finset ℕ :=
  ((Finset.range 127).filter (fun q => 11 ≤ q ∧ (q % 8 = 3 ∨ q % 8 = 5))).image
      (fun q => q * (q ^ 2 - 1) / 2) ∪
  ((Finset.range 127).filter (fun q => 7 ≤ q ∧ (q % 16 = 7 ∨ q % 16 = 9))).image
      (fun q => q * (q ^ 2 - 1) / 2) ∪
  {1080, 2520, 7560, 6048, 2016, 372000, 124000, 95040}

theorem lt_of_psl_card_le {q y : ℕ} (hy : y = q * (q ^ 2 - 1) / 2) (h : y ≤ 1000000) :
    q < 127 := by
  by_contra hc
  push Not at hc
  have h1 : 127 * (127 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
    Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
  omega

theorem mem_F618S {y : ℕ} (h : F618Ord y) (hy : y ≤ 1000000) : y ∈ F618S := by
  rcases h with h | rfl
  · rcases h with ⟨q, hq11, hq, hyq⟩ | ⟨q, hq7, hq, hyq⟩ | rfl | rfl | rfl | ⟨p, e, hp, he, h⟩
    · have := lt_of_psl_card_le hyq hy
      simp only [F618S, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      exact Or.inl (Or.inl ⟨q, ⟨this, hq11, hq⟩, hyq.symm⟩)
    · have := lt_of_psl_card_le hyq hy
      simp only [F618S, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      exact Or.inl (Or.inr ⟨q, ⟨this, hq7, hq⟩, hyq.symm⟩)
    · simp [F618S]
    · simp [F618S]
    · simp [F618S]
    · have hp11 : p < 11 := by
        by_contra hc
        push Not at hc
        have h1 : 11 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc 3
        have h2 : 120 ≤ p ^ 2 - 1 := by have := Nat.pow_le_pow_left hc 2; omega
        have h3 : 1330 ≤ p ^ 3 - 1 := by omega
        have h4 : 1332 ≤ p ^ 3 + 1 := by omega
        rcases he with rfl | rfl <;> rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;>
          first
          | (have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3); omega)
          | (have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h4); omega)
      interval_cases p <;> rcases he with rfl | rfl <;> rcases h with ⟨h8, h⟩ | ⟨h8, h⟩ <;>
        first | omega | (simp [F618S]; omega)
  · simp [F618S]

@[expose] def F618Excl (N : ℕ) : Prop :=
  ∀ x y, x * y = N → Odd x → ¬ 3 ∣ x → ¬ F618Ord y

theorem F618Excl_of_check {N : ℕ} (hN0 : 0 < N) (hN : N ≤ 1000000)
    (h : ∀ y ∈ F618S, ¬ (y ∣ N ∧ N / y % 2 = 1 ∧ ¬ 3 ∣ N / y)) : F618Excl N := by
  intro x y hxy hx hx3 hy
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with rfl | h0
    · simp at hxy; omega
    · exact h0
  have hyN : y ≤ N := Nat.le_of_dvd hN0 ⟨x, by rw [← hxy]; ring⟩
  refine h y (mem_F618S hy (hyN.trans hN)) ⟨⟨x, by rw [← hxy]; ring⟩, ?_, ?_⟩
  · rw [Nat.div_eq_of_eq_mul_left hy0 hxy.symm]; exact Nat.odd_iff.mp hx
  · rw [Nat.div_eq_of_eq_mul_left hy0 hxy.symm]; exact hx3

theorem excl_60 : F618Excl 60 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem excl_504 : F618Excl 504 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem excl_32736 : F618Excl 32736 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem excl_262080 : F618Excl 262080 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem excl_20160 : F618Excl 20160 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem excl_336 : F618Excl 336 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem excl_979200 : F618Excl 979200 :=
  F618Excl_of_check (by norm_num) (by norm_num) (by decide +kernel)

theorem eq_of_two_pow_mul {a n x w u : ℕ} (hx : Odd x) (hw : Odd w) (hu : Odd u)
    (h : x * (2 ^ a * w) = 2 ^ n * u) : a = n := by
  rcases lt_trichotomy a n with hlt | rfl | hgt
  · exfalso
    refine not_two_pow_dvd_of_odd (Nat.odd_mul.mpr ⟨hx, hw⟩) hlt ?_
    rw [show 2 ^ a * (x * w) = 2 ^ n * u by rw [← h]; ring]
    exact Dvd.intro _ rfl
  · rfl
  · exfalso
    refine not_two_pow_dvd_of_odd hu hgt ?_
    rw [← h]
    exact ⟨x * w, by ring⟩

theorem excl_sl_two {n : ℕ} (hn : 2 ≤ n) : F618Excl (2 ^ n * (4 ^ n - 1)) := by
  by_cases h6 : n ≤ 6
  · interval_cases n
    · exact excl_60
    · exact excl_504
    · intro x y hxy hx hx3 hy
      obtain ⟨a, w, hw, rfl, ha⟩ := hy.two_adic
      have := eq_of_two_pow_mul (n := 4) (u := 255) hx hw (by decide) (by rw [hxy]; norm_num)
      omega
    · exact excl_32736
    · exact excl_262080
  · intro x y hxy hx hx3 hy
    have h7 : 2 ^ n ∣ x * y := hxy ▸ Dvd.intro _ rfl
    have hcop : Nat.Coprime (2 ^ n) x := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hx)
    exact hy.not_two_pow_dvd (by omega : 7 ≤ n) (hcop.dvd_of_dvd_mul_left h7)

end CFSG.Quasithin.Gold14610
