module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.N588

open CFSG.Open (ordA ordBC)

theorem ordA_one_eq (q : ℕ) : ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  simp [ordA]

theorem ordA_two_eq (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  rw [ordA, show Finset.Icc 2 (2 + 1) = {2, 3} from by decide, Finset.prod_pair (by norm_num)]

theorem ordBC_two_eq (q : ℕ) :
    ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) := by
  rw [ordBC, show Finset.Icc 1 2 = {1, 2} from by decide, Finset.prod_pair (by norm_num)]

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 :=
  Nat.sub_one_dvd_pow_sub_one q 2

theorem two_mul_ordA_one {q : ℕ} (hq : Odd q) : 2 * ordA 1 q = q * (q ^ 2 - 1) := by
  have h1 : 2 ∣ q - 1 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by omega⟩
  rw [ordA_one_eq, Nat.gcd_eq_left h1]
  exact Nat.mul_div_cancel' ((h1.trans (sub_one_dvd_sq_sub_one q)).mul_left q)

theorem two_mul_ordBC_two {q : ℕ} (hq : Odd q) :
    2 * ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have h1 : 2 ∣ q - 1 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by omega⟩
  rw [ordBC_two_eq, Nat.gcd_eq_left h1]
  exact Nat.mul_div_cancel' (((h1.trans (sub_one_dvd_sq_sub_one q)).mul_right _).mul_left _)

theorem ordA_two_mul_gcd (q : ℕ) :
    ordA 2 q * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  rw [ordA_two_eq]
  exact Nat.div_mul_cancel
    ((((Nat.gcd_dvd_right 3 (q - 1)).trans (sub_one_dvd_sq_sub_one q)).mul_right _).mul_left _)

theorem monotone_l2 : Monotone fun x : ℕ => x * (x ^ 2 - 1) := by
  intro a b h
  dsimp only
  gcongr

theorem l2_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) : x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := by
  have h1 : x ^ 2 - 1 ≤ y ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy.le 2) 1
  have h2 : 0 < y ^ 2 - 1 := by
    have : 2 ≤ y := by omega
    have : 4 ≤ y ^ 2 := by nlinarith
    omega
  calc x * (x ^ 2 - 1) ≤ x * (y ^ 2 - 1) := Nat.mul_le_mul_left _ h1
    _ < y * (y ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hxy h2

theorem eq_of_l2_eq {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x * (x ^ 2 - 1) = y * (y ^ 2 - 1)) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (l2_lt hx hlt).ne
  · exact heq
  · exact absurd h (l2_lt hy hgt).ne'

theorem monotone_l3 : Monotone fun x : ℕ => x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := by
  intro a b h
  dsimp only
  gcongr

theorem monotone_sp4 : Monotone fun x : ℕ => x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1)) := by
  intro a b h
  dsimp only
  gcongr

theorem monotone_l2sq : Monotone fun x : ℕ => x ^ 2 * ((x ^ 2) ^ 2 - 1) := by
  intro a b h
  dsimp only
  gcongr

theorem ne_of_bracket {f : ℕ → ℕ} (hf : Monotone f) {a c : ℕ} (h1 : f a < c)
    (h2 : c < f (a + 1)) (x : ℕ) : f x ≠ c := by
  intro hx
  rcases le_or_gt x a with h | h
  · have := hf h
    omega
  · have := hf (show a + 1 ≤ x by omega)
    omega

theorem false_of_bounds {f : ℕ → ℕ} (hf : Monotone f) {x a b n : ℕ} (hlo : n ≤ f x)
    (hhi : f x ≤ 3 * n) (h1 : f a < n) (h2 : 3 * n < f b) (hx : x ≤ a ∨ b ≤ x) : False := by
  rcases hx with h | h
  · have := hf h
    omega
  · have := hf h
    omega

theorem pow_le_of_dvd_sq_sub_one {p k x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : 2 ≤ x)
    (h : p ^ k ∣ x ^ 2 - 1) : p ^ k ≤ x + 1 := by
  have hfac : x ^ 2 - 1 = (x + 1) * (x - 1) := by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  rw [hfac] at h
  by_cases h1 : p ∣ x + 1
  · by_cases h2 : p ∣ x - 1
    · exfalso
      have h3 : p ∣ (x + 1) - (x - 1) := Nat.dvd_sub h1 h2
      rw [show (x + 1) - (x - 1) = 2 by omega] at h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
    · have hc : Nat.Coprime (p ^ k) (x - 1) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h2)
      exact Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h)
  · have hc : Nat.Coprime (p ^ k) (x + 1) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h1)
    exact (Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h)).trans (by omega)

theorem size_l3 {x : ℕ} (hx : 25 ≤ x) : 2 * (x + 1) ^ 3 < 3 * (x * (x ^ 2 - 1)) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 25 := ⟨x - 25, by omega⟩
  have h : (y + 25) ^ 2 - 1 = y ^ 2 + 50 * y + 624 := by
    have : (y + 25) ^ 2 = y ^ 2 + 50 * y + 625 := by ring
    omega
  rw [h]
  ring_nf
  nlinarith [sq_nonneg y]

theorem size_sp4 {x : ℕ} (hx : 25 ≤ x) : (x + 1) ^ 3 < 9 * (x * (x ^ 2 - 1)) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 25 := ⟨x - 25, by omega⟩
  have h : (y + 25) ^ 2 - 1 = y ^ 2 + 50 * y + 624 := by
    have : (y + 25) ^ 2 = y ^ 2 + 50 * y + 625 := by ring
    omega
  rw [h]
  ring_nf
  nlinarith [sq_nonneg y]

@[expose] def List318 (r n : ℕ) : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (n = ordA 1 p ∨ n = ordA 2 p)) ∨ n = 360 ∨ n = 2520 ∨
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ r ∧ (n = ordBC 2 p ∨ n = ordA 1 (p ^ 2))

theorem bounds_l3 {n q : ℕ} (h : n = ordA 2 q) :
    n ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∧ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * n := by
  have hg := ordA_two_mul_gcd q
  rw [← h] at hg
  have hg1 : 1 ≤ Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  refine ⟨(Nat.le_mul_of_pos_right n hg1).trans hg.le, hg.symm.le.trans ?_⟩
  rw [mul_comm 3 n]
  exact Nat.mul_le_mul_left n hg3

theorem false_of_fixed {r n : ℕ} (hn : n = 7920 ∨ n = 20160 ∨ n = 17971200 ∨ n = 1814400)
    (h318 : List318 r n) : False := by
  rcases h318 with ⟨p, hp, hp2, h | h⟩ | h | h | ⟨p, hp, hp2, -, h | h⟩
  · have h2 := two_mul_ordA_one (hp.odd_of_ne_two hp2)
    rw [← h] at h2
    rcases hn with rfl | rfl | rfl | rfl
    · exact ne_of_bracket monotone_l2 (a := 25) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_l2 (a := 34) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_l2 (a := 330) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_l2 (a := 153) (by norm_num) (by norm_num) p h2.symm
  · obtain ⟨hlo, hhi⟩ := bounds_l3 h
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have h9 : p ≠ 9 := by
      rintro rfl
      norm_num at hp
    rcases hn with rfl | rfl | rfl | rfl
    · exact false_of_bounds monotone_l3 hlo hhi (a := 3) (b := 4) (by norm_num) (by norm_num)
        (by omega)
    · exact false_of_bounds monotone_l3 hlo hhi (a := 3) (b := 5) (by norm_num) (by norm_num)
        (by omega)
    · exact false_of_bounds monotone_l3 hlo hhi (a := 8) (b := 10) (by norm_num) (by norm_num)
        (by omega)
    · exact false_of_bounds monotone_l3 hlo hhi (a := 6) (b := 7) (by norm_num) (by norm_num)
        (by omega)
  · rcases hn with rfl | rfl | rfl | rfl <;> norm_num at h
  · rcases hn with rfl | rfl | rfl | rfl <;> norm_num at h
  · have h2 := two_mul_ordBC_two (hp.odd_of_ne_two hp2)
    rw [← h] at h2
    rcases hn with rfl | rfl | rfl | rfl
    · exact ne_of_bracket monotone_sp4 (a := 2) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_sp4 (a := 2) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_sp4 (a := 5) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_sp4 (a := 4) (by norm_num) (by norm_num) p h2.symm
  · have h2 := two_mul_ordA_one ((hp.odd_of_ne_two hp2).pow (n := 2))
    rw [← h] at h2
    rcases hn with rfl | rfl | rfl | rfl
    · exact ne_of_bracket monotone_l2sq (a := 5) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_l2sq (a := 5) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_l2sq (a := 18) (by norm_num) (by norm_num) p h2.symm
    · exact ne_of_bracket monotone_l2sq (a := 12) (by norm_num) (by norm_num) p h2.symm

theorem false_of_l2sq {r n : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hn : n = ordA 1 (r ^ 2))
    (h318 : List318 r n) : False := by
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  set x := r ^ 2 with hx
  have hx25 : 25 ≤ x := by nlinarith
  have hxn : 2 * n = x * (x ^ 2 - 1) := by
    rw [hn]
    exact two_mul_ordA_one hrodd.pow
  have hx15600 : 15600 ≤ x * (x ^ 2 - 1) := monotone_l2 hx25
  rcases h318 with ⟨p, hp, hp2, h | h⟩ | h | h | ⟨p, hp, hp2, hpr, h | h⟩
  ·
    have h2 := two_mul_ordA_one (hp.odd_of_ne_two hp2)
    rw [← h, hxn] at h2
    have hpx : x = p := eq_of_l2_eq (by omega) hp.one_lt.le h2
    rw [← hpx, hx] at hp
    exact Nat.Prime.not_prime_pow le_rfl hp
  ·
    have hg := ordA_two_mul_gcd p
    rw [← h] at hg
    have hp3n : p ^ 3 ∣ n := by
      have hdvd : p ^ 3 ∣ n * Nat.gcd 3 (p - 1) := hg ▸ dvd_mul_right _ _
      have hcop : Nat.Coprime (p ^ 3) (Nat.gcd 3 (p - 1)) := by
        apply Nat.Coprime.pow_left
        by_cases hp3 : p = 3
        · subst hp3
          norm_num
        · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _)
            ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
      exact hcop.dvd_of_dvd_mul_right hdvd
    have h1 : p ^ 3 ∣ x * (x ^ 2 - 1) := hxn ▸ dvd_mul_of_dvd_right hp3n 2
    by_cases hpr : p = r
    ·
      subst hpr
      have h2 : p ∣ x ^ 2 - 1 := by
        rw [hx, pow_succ p 2] at h1
        exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
      have h3 : p ∣ x ^ 2 := dvd_pow (hx ▸ dvd_pow_self p two_ne_zero) two_ne_zero
      have h4 : p ∣ 1 := by
        have := Nat.dvd_sub h3 h2
        rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
    ·
      have hcop : Nat.Coprime (p ^ 3) x := by
        rw [hx]
        exact Nat.Coprime.pow 3 2 ((Nat.coprime_primes hp hr).2 hpr)
      have h3 : p ^ 3 ≤ x + 1 :=
        pow_le_of_dvd_sq_sub_one hp hp2 (by omega) (hcop.dvd_of_dvd_mul_left h1)
      have h4 : n ≤ p ^ 8 := by
        calc n ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := (bounds_l3 h).1
          _ ≤ p ^ 3 * (p ^ 2 * p ^ 3) := by gcongr <;> exact Nat.sub_le _ _
          _ = p ^ 8 := by ring
      have h5 : 3 * p ^ 8 ≤ (x + 1) ^ 3 := by
        have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        calc 3 * p ^ 8 ≤ p * p ^ 8 := Nat.mul_le_mul_right _ hp3
          _ = (p ^ 3) ^ 3 := by ring
          _ ≤ (x + 1) ^ 3 := Nat.pow_le_pow_left h3 3
      have h6 := size_l3 hx25
      omega
  · omega
  · omega
  ·
    have h2 := two_mul_ordBC_two (hp.odd_of_ne_two hp2)
    rw [← h, hxn] at h2
    have h1 : p ^ 4 ∣ x * (x ^ 2 - 1) := h2 ▸ dvd_mul_right _ _
    have hcop : Nat.Coprime (p ^ 4) x := by
      rw [hx]
      exact Nat.Coprime.pow 4 2 ((Nat.coprime_primes hp hr).2 hpr)
    have h3 : p ^ 4 ≤ x + 1 :=
      pow_le_of_dvd_sq_sub_one hp hp2 (by omega) (hcop.dvd_of_dvd_mul_left h1)
    have h4 : p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) ≤ p ^ 10 := by
      calc p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) ≤ p ^ 4 * (p ^ 2 * p ^ 4) := by
            gcongr <;> exact Nat.sub_le _ _
        _ = p ^ 10 := by ring
    have h5 : 9 * p ^ 10 ≤ (x + 1) ^ 3 := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      calc 9 * p ^ 10 ≤ p ^ 2 * p ^ 10 := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (p ^ 4) ^ 3 := by ring
        _ ≤ (x + 1) ^ 3 := Nat.pow_le_pow_left h3 3
    have h6 := size_sp4 hx25
    omega
  ·
    have h2 := two_mul_ordA_one ((hp.odd_of_ne_two hp2).pow (n := 2))
    rw [← h, hxn] at h2
    have hpx : x = p ^ 2 := eq_of_l2_eq (by omega) (Nat.one_le_pow _ _ hp.pos) h2
    rw [hx] at hpx
    exact hpr (Nat.pow_left_injective two_ne_zero hpx).symm

theorem false_of_orders {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h620 : (r ≠ 3 ∧ n = ordA 1 (r ^ 2)) ∨ n = 7920 ∨ n = 20160 ∨ n = 17971200 ∨ n = 1814400)
    (h318 : List318 r n) : False := by
  rcases h620 with ⟨hr3, hn⟩ | hn
  · have hr5 : 5 ≤ r := by
      have := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    exact false_of_l2sq hr hr5 hn h318
  · exact false_of_fixed hn h318

end CFSG.LocalAnalysis.UniquenessCase.UC6.N588
