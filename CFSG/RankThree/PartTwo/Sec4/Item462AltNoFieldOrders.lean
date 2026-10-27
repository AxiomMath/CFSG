module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

def ordSL (q : ℕ) : ℕ := q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)

def ordSU (q : ℕ) : ℕ := q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)

section Arith

variable {p : ℕ}

theorem not_dvd_sub_one [hp : Fact p.Prime] {m : ℕ} (hm : p ∣ m) (h1 : 1 ≤ m) :
    ¬ p ∣ m - 1 := by
  intro h
  have h' : p ∣ m - (m - 1) := Nat.dvd_sub hm h
  rw [Nat.sub_sub_self h1] at h'
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp h')

theorem not_dvd_add_one [hp : Fact p.Prime] {m : ℕ} (hm : p ∣ m) :
    ¬ p ∣ m + 1 := by
  intro h
  have h' : p ∣ m + 1 - m := Nat.dvd_sub h hm
  rw [Nat.add_sub_cancel_left] at h'
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp h')

theorem one_lt_pow_of_two_le {q k : ℕ} (hq : 2 ≤ q) (hk : k ≠ 0) : 1 < q ^ k :=
  lt_of_lt_of_le one_lt_two (le_trans hq (le_self_pow (by omega) hk))

theorem padicValNat_core [hp : Fact p.Prime] {q e t : ℕ} (hqv : padicValNat p q = e)
    (hpq : p ∣ q) (hq2 : 2 ≤ q) (ht0 : t ≠ 0) (htp : ¬ p ∣ t) :
    padicValNat p (q ^ 3 * (q ^ 2 - 1) * t) = 3 * e := by
  have h1 : 1 < q ^ 2 := one_lt_pow_of_two_le hq2 (by norm_num)
  have hq0 : q ≠ 0 := by omega
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq0
  have h2ne : q ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt h1
  have hn2 : ¬ p ∣ q ^ 2 - 1 :=
    not_dvd_sub_one (dvd_pow hpq (by norm_num)) (Nat.le_of_lt h1)
  have h3 : padicValNat p (q ^ 3) = 3 * e := by
    rw [padicValNat.pow, hqv]
  have e1 : padicValNat p (q ^ 3 * (q ^ 2 - 1) * t)
      = padicValNat p (q ^ 3 * (q ^ 2 - 1)) + padicValNat p t :=
    padicValNat.mul (mul_ne_zero hq3 h2ne) ht0
  have e2 : padicValNat p (q ^ 3 * (q ^ 2 - 1))
      = padicValNat p (q ^ 3) + padicValNat p (q ^ 2 - 1) :=
    padicValNat.mul hq3 h2ne
  have e3 : padicValNat p (q ^ 2 - 1) = 0 := padicValNat.eq_zero_of_not_dvd hn2
  have e4 : padicValNat p t = 0 := padicValNat.eq_zero_of_not_dvd htp
  omega

theorem padicValNat_eq_of_mul_eq [hp : Fact p.Prime] {N c M : ℕ} (hc : ¬ p ∣ c)
    (hc0 : c ≠ 0) (hM : M ≠ 0) (hN : N * c = M) : padicValNat p N = padicValNat p M := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM (by rw [← hN, zero_mul])
  rw [← hN, padicValNat.mul (p := p) hN0 hc0, padicValNat.eq_zero_of_not_dvd hc, add_zero]

theorem not_dvd_of_c [hp : Fact p.Prime] (h5 : 5 ≤ p) {c : ℕ} (hc : c = 1 ∨ c = 3) :
    ¬ p ∣ c ∧ c ≠ 0 := by
  rcases hc with rfl | rfl
  · exact ⟨hp.out.not_dvd_one, one_ne_zero⟩
  · refine ⟨fun h => ?_, by norm_num⟩
    have := Nat.le_of_dvd (by norm_num) h
    omega

theorem padicValNat_ordSL [hp : Fact p.Prime] (h5 : 5 ≤ p) {e N c : ℕ} (he : 1 ≤ e)
    (hc : c = 1 ∨ c = 3) (hN : N * c = ordSL (p ^ e)) :
    padicValNat p N = 3 * e := by
  have hp0 : 0 < p := by omega
  have hpe : p ≤ p ^ e := le_self_pow (by omega) (by omega)
  have hq2 : 2 ≤ p ^ e := le_trans (by omega) hpe
  have hpq : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hqv : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
  have hq3 : 1 < (p ^ e) ^ 3 := one_lt_pow_of_two_le hq2 (by norm_num)
  have hq2' : 1 < (p ^ e) ^ 2 := one_lt_pow_of_two_le hq2 (by norm_num)
  have hM : padicValNat p (ordSL (p ^ e)) = 3 * e :=
    padicValNat_core hqv hpq hq2 (Nat.sub_ne_zero_of_lt hq3)
      (not_dvd_sub_one (dvd_pow hpq (by norm_num)) (Nat.le_of_lt hq3))
  have hM0 : ordSL (p ^ e) ≠ 0 := by
    unfold ordSL
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 (pow_pos hp0 e).ne')
      (Nat.sub_ne_zero_of_lt hq2')) (Nat.sub_ne_zero_of_lt hq3)
  obtain ⟨hpc, hc0⟩ := not_dvd_of_c h5 hc
  exact (padicValNat_eq_of_mul_eq hpc hc0 hM0 hN).trans hM

theorem padicValNat_ordSU [hp : Fact p.Prime] (h5 : 5 ≤ p) {e N c : ℕ} (he : 1 ≤ e)
    (hc : c = 1 ∨ c = 3) (hN : N * c = ordSU (p ^ e)) :
    padicValNat p N = 3 * e := by
  have hp0 : 0 < p := by omega
  have hpe : p ≤ p ^ e := le_self_pow (by omega) (by omega)
  have hq2 : 2 ≤ p ^ e := le_trans (by omega) hpe
  have hpq : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hqv : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
  have hq3 : 1 < (p ^ e) ^ 3 := one_lt_pow_of_two_le hq2 (by norm_num)
  have hq2' : 1 < (p ^ e) ^ 2 := one_lt_pow_of_two_le hq2 (by norm_num)
  have hM : padicValNat p (ordSU (p ^ e)) = 3 * e :=
    padicValNat_core hqv hpq hq2 (by omega)
      (not_dvd_add_one (dvd_pow hpq (by norm_num)))
  have hM0 : ordSU (p ^ e) ≠ 0 := by
    unfold ordSU
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 (pow_pos hp0 e).ne')
      (Nat.sub_ne_zero_of_lt hq2')) (by omega)
  obtain ⟨hpc, hc0⟩ := not_dvd_of_c h5 hc
  exact (padicValNat_eq_of_mul_eq hpc hc0 hM0 hN).trans hM

theorem pow_padic_le_of_split {l u v w B : ℕ} [hl : Fact l.Prime]
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (huv : ¬ (l ∣ u ∧ l ∣ v)) (huw : ¬ (l ∣ u ∧ l ∣ w)) (hvw : ¬ (l ∣ v ∧ l ∣ w))
    (hu2 : u ^ 2 ≤ B) (hv' : v ≤ B) (hw' : w ≤ B) (hB : 1 ≤ B) :
    l ^ padicValNat l (u ^ 2 * v * w) ≤ B := by
  have hu2ne : u ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  have hval : padicValNat l (u ^ 2 * v * w)
      = padicValNat l (u ^ 2) + padicValNat l v + padicValNat l w := by
    rw [padicValNat.mul (mul_ne_zero hu2ne hv.ne') hw.ne', padicValNat.mul hu2ne hv.ne']
  rw [hval, padicValNat.pow]
  by_cases h1 : l ∣ u
  · have h2 : ¬ l ∣ v := fun h => huv ⟨h1, h⟩
    have h3 : ¬ l ∣ w := fun h => huw ⟨h1, h⟩
    rw [padicValNat.eq_zero_of_not_dvd h2, padicValNat.eq_zero_of_not_dvd h3]
    have hd : l ^ padicValNat l u ≤ u := Nat.le_of_dvd hu pow_padicValNat_dvd
    have hsq : l ^ (2 * padicValNat l u + 0 + 0) = (l ^ padicValNat l u) ^ 2 := by
      rw [add_zero, add_zero, ← pow_mul, mul_comm]
    rw [hsq]
    exact le_trans (Nat.pow_le_pow_left hd 2) hu2
  · by_cases h2 : l ∣ v
    · have h3 : ¬ l ∣ w := fun h => hvw ⟨h2, h⟩
      rw [padicValNat.eq_zero_of_not_dvd h1, padicValNat.eq_zero_of_not_dvd h3]
      have hd : l ^ padicValNat l v ≤ v := Nat.le_of_dvd hv pow_padicValNat_dvd
      have hsq : l ^ (2 * 0 + padicValNat l v + 0) = l ^ padicValNat l v := by
        rw [mul_zero, zero_add, add_zero]
      rw [hsq]
      exact le_trans hd hv'
    · by_cases h3 : l ∣ w
      · rw [padicValNat.eq_zero_of_not_dvd h1, padicValNat.eq_zero_of_not_dvd h2]
        have hd : l ^ padicValNat l w ≤ w := Nat.le_of_dvd hw pow_padicValNat_dvd
        have hsq : l ^ (2 * 0 + 0 + padicValNat l w) = l ^ padicValNat l w := by
          rw [mul_zero, zero_add, zero_add]
        rw [hsq]
        exact le_trans hd hw'
      · rw [padicValNat.eq_zero_of_not_dvd h1, padicValNat.eq_zero_of_not_dvd h2,
          padicValNat.eq_zero_of_not_dvd h3]
        simpa using hB

theorem ordSL_succ (r : ℕ) :
    ordSL (r + 1) = (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) := by
  unfold ordSL
  have h1 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (r + 1) ^ 3 - 1 = r * (r ^ 2 + 3 * r + 3) := Nat.sub_eq_of_eq_add (by ring)
  rw [h1, h2]
  ring

theorem ordSU_succ (r : ℕ) :
    ordSU (r + 1) = (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
  unfold ordSU
  have h1 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [h1]
  ring

theorem poly_bound_SL {r : ℕ} (hr : 4 ≤ r) :
    3 * (r + 2) ^ 6 ≤ (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) := by
  by_cases h14 : 14 ≤ r
  · have hA : 3 * (r + 2) ^ 6 ≤ 192 * r ^ 6 := by
      have : (r + 2) ^ 6 ≤ (2 * r) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      nlinarith
    have hB : r ^ 8 ≤ (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) := by
      calc r ^ 8 = r ^ 3 * (r ^ 2 * r * r ^ 2) := by ring
        _ ≤ (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3)
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith))
    have hC : 192 * r ^ 6 ≤ r ^ 8 := by
      have h192 : 192 ≤ r ^ 2 := by nlinarith
      calc 192 * r ^ 6 ≤ r ^ 2 * r ^ 6 := Nat.mul_le_mul_right (r ^ 6) h192
        _ = r ^ 8 := by ring
    omega
  · push Not at h14
    interval_cases r <;> norm_num

theorem poly_bound_SU {r : ℕ} (hr : 4 ≤ r) :
    3 * (r + 2) ^ 6 ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
  by_cases h14 : 14 ≤ r
  · have hA : 3 * (r + 2) ^ 6 ≤ 192 * r ^ 6 := by
      have : (r + 2) ^ 6 ≤ (2 * r) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      nlinarith
    have hB : r ^ 8 ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
      calc r ^ 8 = r ^ 3 * (r ^ 2 * (r * r ^ 2)) := by ring
        _ ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3)
            (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2)
              (Nat.mul_le_mul_left r (by omega)))
    have hC : 192 * r ^ 6 ≤ r ^ 8 := by
      have h192 : 192 ≤ r ^ 2 := by nlinarith
      calc 192 * r ^ 6 ≤ r ^ 2 * r ^ 6 := Nat.mul_le_mul_right (r ^ 6) h192
        _ = r ^ 8 := by ring
    omega
  · push Not at h14
    interval_cases r <;> norm_num

theorem dvd_two_of_SL {l r : ℕ} (hl : l ∣ r) (hv : l ∣ r + 2) : l ∣ 2 :=
  (Nat.dvd_add_right hl).mp hv

theorem dvd_three_of_SL_uw {l r : ℕ} (hl : l ∣ r) (hw : l ∣ r ^ 2 + 3 * r + 3) : l ∣ 3 := by
  have h : r ^ 2 + 3 * r + 3 = r * (r + 3) + 3 := by ring
  rw [h] at hw
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hl (r + 3))).mp hw

theorem dvd_one_of_SL_vw {l r : ℕ} (hv : l ∣ r + 2) (hw : l ∣ r ^ 2 + 3 * r + 3) : l ∣ 1 := by
  have h : r ^ 2 + 3 * r + 3 = (r + 2) * (r + 1) + 1 := by ring
  rw [h] at hw
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hv (r + 1))).mp hw

theorem dvd_three_of_SU_uw {l r : ℕ} (hr : 1 ≤ r) (hu : l ∣ r + 2) (hw : l ∣ r ^ 2 + r + 1) :
    l ∣ 3 := by
  have h2 : r ^ 2 + r + 1 = (r + 2) * (r - 1) + 3 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hs : s + 1 - 1 = s := by omega
    rw [hs]
    ring
  rw [h2] at hw
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hu (r - 1))).mp hw

theorem dvd_one_of_SU_vw {l r : ℕ} (hv : l ∣ r) (hw : l ∣ r ^ 2 + r + 1) : l ∣ 1 := by
  have h : r ^ 2 + r + 1 = r * (r + 1) + 1 := by ring
  rw [h] at hw
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hv (r + 1))).mp hw

theorem pow_cube_val_le {l N c A u v w B : ℕ} [hl : Fact l.Prime]
    (hc : c = 1 ∨ c = 3) (hlc : ¬ l ∣ c) (hlA : ¬ l ∣ A) (hA : A ≠ 0)
    (hM : N * c = A * (u ^ 2 * v * w))
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (huv : ¬ (l ∣ u ∧ l ∣ v)) (huw : ¬ (l ∣ u ∧ l ∣ w)) (hvw : ¬ (l ∣ v ∧ l ∣ w))
    (hu2 : u ^ 2 ≤ B) (hv' : v ≤ B) (hw' : w ≤ B) (hB : 1 ≤ B)
    (hbig : 3 * B ^ 3 ≤ A * (u ^ 2 * v * w)) :
    l ^ (3 * padicValNat l N) ≤ N := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have hpos : u ^ 2 * v * w ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hu.ne') hv.ne') hw.ne'
  have hM0 : A * (u ^ 2 * v * w) ≠ 0 := mul_ne_zero hA hpos
  have hvN : padicValNat l N = padicValNat l (u ^ 2 * v * w) := by
    rw [padicValNat_eq_of_mul_eq hlc hc0 hM0 hM, padicValNat.mul (p := l) hA hpos,
      padicValNat.eq_zero_of_not_dvd hlA, zero_add]
  have hle : l ^ padicValNat l N ≤ B := by
    rw [hvN]
    exact pow_padic_le_of_split hu hv hw huv huw hvw hu2 hv' hw' hB
  have hN : B ^ 3 ≤ N := by
    have h3 : 3 * B ^ 3 ≤ N * c := by rw [hM]; exact hbig
    rcases hc with rfl | rfl <;> omega
  calc l ^ (3 * padicValNat l N) = (l ^ padicValNat l N) ^ 3 := by
        rw [mul_comm, pow_mul]
    _ ≤ B ^ 3 := Nat.pow_le_pow_left hle 3
    _ ≤ N := hN

theorem cube_val_le_SL {l N c r : ℕ} [hl : Fact l.Prime] (h5 : 5 ≤ l) (hr : 4 ≤ r)
    (hc : c = 1 ∨ c = 3) (hlq : ¬ l ∣ r + 1) (hM : N * c = ordSL (r + 1)) :
    l ^ (3 * padicValNat l N) ≤ N := by
  have hlc : ¬ l ∣ c := by
    rcases hc with rfl | rfl
    · exact hl.out.not_dvd_one
    · intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
  have hlA : ¬ l ∣ (r + 1) ^ 3 := fun h => hlq (hl.out.dvd_of_dvd_pow h)
  rw [ordSL_succ] at hM
  refine pow_cube_val_le (B := (r + 2) ^ 2) hc hlc hlA (pow_ne_zero 3 (by omega)) hM
    (by omega) (by omega) (by positivity) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => by
      have := Nat.le_of_dvd (by norm_num) (dvd_two_of_SL h.1 h.2)
      omega
  · exact fun h => by
      have := Nat.le_of_dvd (by norm_num) (dvd_three_of_SL_uw h.1 h.2)
      omega
  · exact fun h => hl.out.not_dvd_one (dvd_one_of_SL_vw h.1 h.2)
  · exact Nat.pow_le_pow_left (by omega) 2
  · nlinarith
  · nlinarith
  · nlinarith
  · rw [show ((r + 2) ^ 2) ^ 3 = (r + 2) ^ 6 by ring]
    exact poly_bound_SL hr

theorem dvd_two_of_SU {l r : ℕ} (hv : l ∣ r) (hu : l ∣ r + 2) : l ∣ 2 :=
  (Nat.dvd_add_right hv).mp hu

theorem cube_val_le_SU {l N c r : ℕ} [hl : Fact l.Prime] (h5 : 5 ≤ l) (hr : 4 ≤ r)
    (hc : c = 1 ∨ c = 3) (hlq : ¬ l ∣ r + 1) (hM : N * c = ordSU (r + 1)) :
    l ^ (3 * padicValNat l N) ≤ N := by
  have hlc : ¬ l ∣ c := by
    rcases hc with rfl | rfl
    · exact hl.out.not_dvd_one
    · intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
  have hlA : ¬ l ∣ (r + 1) ^ 3 := fun h => hlq (hl.out.dvd_of_dvd_pow h)
  rw [ordSU_succ, show (r + 2) ^ 2 * (r * (r ^ 2 + r + 1))
    = (r + 2) ^ 2 * r * (r ^ 2 + r + 1) by ring] at hM
  refine pow_cube_val_le (B := (r + 2) ^ 2) hc hlc hlA (pow_ne_zero 3 (by omega)) hM
    (by omega) (by omega) (by positivity) ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_
  · exact fun h => by
      have := Nat.le_of_dvd (by norm_num) (dvd_two_of_SU h.2 h.1)
      omega
  · exact fun h => by
      have := Nat.le_of_dvd (by norm_num) (dvd_three_of_SU_uw (by omega) h.1 h.2)
      omega
  · exact fun h => hl.out.not_dvd_one (dvd_one_of_SU_vw h.1 h.2)
  · nlinarith
  · nlinarith
  · nlinarith
  · rw [show ((r + 2) ^ 2) ^ 3 = (r + 2) ^ 6 by ring,
      show (r + 2) ^ 2 * r * (r ^ 2 + r + 1) = (r + 2) ^ 2 * (r * (r ^ 2 + r + 1)) by ring]
    exact poly_bound_SU hr

theorem pow_padic_mul_le {l a b B1 B2 : ℕ} [hl : Fact l.Prime] (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : l ^ padicValNat l a ≤ B1) (h2 : l ^ padicValNat l b ≤ B2) :
    l ^ padicValNat l (a * b) ≤ B1 * B2 := by
  rw [padicValNat.mul (p := l) ha hb, pow_add]
  exact Nat.mul_le_mul h1 h2

theorem pow_padic_sq_le {l a B : ℕ} [hl : Fact l.Prime] (h : l ^ padicValNat l a ≤ B) :
    l ^ padicValNat l (a ^ 2) ≤ B ^ 2 := by
  rw [padicValNat.pow, mul_comm, pow_mul]
  exact Nat.pow_le_pow_left h 2

theorem pow_padic_le_of_not_sq {l a : ℕ} [hl : Fact l.Prime] (h : ¬ l ^ 2 ∣ a) :
    l ^ padicValNat l a ≤ l := by
  have hv : padicValNat l a < 2 := by
    by_contra hc
    push Not at hc
    exact h (dvd_trans (pow_dvd_pow l hc) pow_padicValNat_dvd)
  calc l ^ padicValNat l a ≤ l ^ 1 := Nat.pow_le_pow_right hl.out.pos (by omega)
    _ = l := pow_one l

theorem pow_padic_le_self {l a : ℕ} [hl : Fact l.Prime] (ha : a ≠ 0) :
    l ^ padicValNat l a ≤ a :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero ha) pow_padicValNat_dvd

theorem pow_padic_le_one {l a : ℕ} [hl : Fact l.Prime] (h : ¬ l ∣ a) :
    l ^ padicValNat l a ≤ 1 := by
  simp [padicValNat.eq_zero_of_not_dvd h]

theorem cube_val_le_of_bound {l N c B : ℕ} (hc : c = 1 ∨ c = 3)
    (hle : l ^ padicValNat l N ≤ B) (hbig : 3 * B ^ 3 ≤ N * c) :
    l ^ (3 * padicValNat l N) ≤ N := by
  have hN : B ^ 3 ≤ N := by
    rcases hc with rfl | rfl <;> omega
  calc l ^ (3 * padicValNat l N) = (l ^ padicValNat l N) ^ 3 := by
        rw [mul_comm, pow_mul]
    _ ≤ B ^ 3 := Nat.pow_le_pow_left hle 3
    _ ≤ N := hN

theorem padicValNat_le_of_mul_eq {l N c M : ℕ} [hl : Fact l.Prime] (hN : N ≠ 0) (hc0 : c ≠ 0)
    (hM : N * c = M) : padicValNat l N ≤ padicValNat l M := by
  rw [← hM, padicValNat.mul (p := l) hN hc0]
  omega

theorem cube_val_le_of_mul {l N c M B : ℕ} [hl : Fact l.Prime] (hc : c = 1 ∨ c = 3)
    (hN : N ≠ 0) (hM : N * c = M) (hle : l ^ padicValNat l M ≤ B)
    (hbig : 3 * B ^ 3 ≤ M) : l ^ (3 * padicValNat l N) ≤ N := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have h1 : l ^ padicValNat l N ≤ B :=
    le_trans (Nat.pow_le_pow_right hl.out.pos (padicValNat_le_of_mul_eq hN hc0 hM)) hle
  exact cube_val_le_of_bound hc h1 (by rw [hM]; exact hbig)

theorem two_SL_A {r : ℕ} (hr : 4 ≤ r) (h4 : r % 4 = 0) :
    2 ^ padicValNat 2 (ordSL (r + 1)) ≤ 2 * r ^ 2 := by
  rw [ordSL_succ]
  have hev : 2 ∣ r := by omega
  have hA : ¬ (2 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hW : ¬ (2 ∣ r ^ 2 + 3 * r + 3) := by
    intro h
    have h1 : 2 ∣ r ^ 2 + 3 * r :=
      dvd_add (dvd_pow hev (by norm_num)) (dvd_mul_of_dvd_right hev 3)
    have h2 : 2 ∣ 3 := (Nat.dvd_add_right h1).mp h
    omega
  have hR : 2 ^ padicValNat 2 (r + 2) ≤ 2 := by
    apply pow_padic_le_of_not_sq
    intro h4'
    norm_num at h4'
    omega
  have hL : 2 ^ padicValNat 2 r ≤ r := pow_padic_le_self (by omega)
  have hX : 2 ^ padicValNat 2 (r ^ 2 * (r + 2)) ≤ r ^ 2 * 2 :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (by omega) (pow_padic_sq_le hL) hR
  have hY : 2 ^ padicValNat 2 (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) ≤ r ^ 2 * 2 * 1 :=
    pow_padic_mul_le (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity)
      hX (pow_padic_le_one hW)
  have hZ : 2 ^ padicValNat 2 ((r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)))
      ≤ 1 * (r ^ 2 * 2 * 1) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity))
      (pow_padic_le_one hA) hY
  exact le_of_le_of_eq hZ (by ring)

theorem poly_SL_A {r : ℕ} (hr : 4 ≤ r) :
    3 * (2 * r ^ 2) ^ 3 ≤ (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  have h : ((s + 4) + 1) ^ 3 * ((s + 4) ^ 2 * ((s + 4) + 2) * ((s + 4) ^ 2 + 3 * (s + 4) + 3)) = 3 * (2 * (s + 4) ^ 2) ^ 3 + (273696 + 455744 * s + 334730 * s ^ 2 + 141531 * s ^ 3 + 37590 * s ^ 4 + 6393 * s ^ 5 + 675 * s ^ 6 + 40 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem poly_SL_B {r : ℕ} (hr : 4 ≤ r) :
    3 * (4 * (r + 2)) ^ 3 ≤ (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  have h : ((s + 4) + 1) ^ 3 * ((s + 4) ^ 2 * ((s + 4) + 2) * ((s + 4) ^ 2 + 3 * (s + 4) + 3)) = 3 * (4 * ((s + 4) + 2)) ^ 3 + (330528 + 582464 * s + 423434 * s ^ 2 + 172059 * s ^ 3 + 43350 * s ^ 4 + 6969 * s ^ 5 + 699 * s ^ 6 + 40 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem poly_SL_C {r : ℕ} (hr : 4 ≤ r) :
    3 * (3 * r ^ 2) ^ 3 ≤ (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  have h : ((s + 4) + 1) ^ 3 * ((s + 4) ^ 2 * ((s + 4) + 2) * ((s + 4) ^ 2 + 3 * (s + 4) + 3)) = 3 * (3 * (s + 4) ^ 2) ^ 3 + (40224 + 105536 * s + 115850 * s ^ 2 + 68571 * s ^ 3 + 23910 * s ^ 4 + 5025 * s ^ 5 + 618 * s ^ 6 + 40 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem poly_SU_A {r : ℕ} (hr : 4 ≤ r) :
    3 * (4 * r) ^ 3 ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  have h : ((s + 4) + 1) ^ 3 * (((s + 4) + 2) ^ 2 * ((s + 4) * ((s + 4) ^ 2 + (s + 4) + 1))) = 3 * (4 * (s + 4)) ^ 3 + (365712 + 600084 * s + 427056 * s ^ 2 + 172557 * s ^ 3 + 43400 * s ^ 4 + 6971 * s ^ 5 + 699 * s ^ 6 + 40 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem poly_SU_B {r : ℕ} (hr : 10 ≤ r) :
    3 * (2 * (r + 2) ^ 2) ^ 3 ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 10 := ⟨r - 10, by omega⟩
  have h : ((s + 10) + 1) ^ 3 * (((s + 10) + 2) ^ 2 * ((s + 10) * ((s + 10) ^ 2 + (s + 10) + 1))) = 3 * (2 * ((s + 10) + 2) ^ 2) ^ 3 + (141083424 + 119172096 * s + 41932410 * s ^ 2 + 8164005 * s ^ 3 + 971270 * s ^ 4 + 72743 * s ^ 5 + 3363 * s ^ 6 + 88 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem poly_SU_C {r : ℕ} (hr : 4 ≤ r) :
    3 * (27) ^ 3 ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  have h : ((s + 4) + 1) ^ 3 * (((s + 4) + 2) ^ 2 * ((s + 4) * ((s + 4) ^ 2 + (s + 4) + 1))) = 3 * (27) ^ 3 + (318951 + 609300 * s + 429360 * s ^ 2 + 172749 * s ^ 3 + 43400 * s ^ 4 + 6971 * s ^ 5 + 699 * s ^ 6 + 40 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem poly_SU_D {r : ℕ} (hr : 16 ≤ r) :
    3 * (3 * (r + 2) ^ 2) ^ 3 ≤ (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 16 := ⟨r - 16, by omega⟩
  have h : ((s + 16) + 1) ^ 3 * (((s + 16) + 2) ^ 2 * ((s + 16) * ((s + 16) ^ 2 + (s + 16) + 1))) = 3 * (3 * ((s + 16) + 2) ^ 2) ^ 3 + (4198044672 + 2356276932 * s + 547102356 * s ^ 2 + 69968781 * s ^ 3 + 5448560 * s ^ 4 + 266279 * s ^ 5 + 8010 * s ^ 6 + 136 * s ^ 7 + 1 * s ^ 8) := by ring
  exact le_of_le_of_eq (Nat.le_add_right _ _) h.symm

theorem two_SL_B {r : ℕ} (hr : 4 ≤ r) (h4 : r % 4 = 2) :
    2 ^ padicValNat 2 (ordSL (r + 1)) ≤ 4 * (r + 2) := by
  rw [ordSL_succ]
  have hev : 2 ∣ r := by omega
  have hA : ¬ (2 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hW : ¬ (2 ∣ r ^ 2 + 3 * r + 3) := by
    intro h
    have h1 : 2 ∣ r ^ 2 + 3 * r :=
      dvd_add (dvd_pow hev (by norm_num)) (dvd_mul_of_dvd_right hev 3)
    have h2 : 2 ∣ 3 := (Nat.dvd_add_right h1).mp h
    omega
  have hL : 2 ^ padicValNat 2 r ≤ 2 := by
    apply pow_padic_le_of_not_sq
    intro h4'
    norm_num at h4'
    omega
  have hR : 2 ^ padicValNat 2 (r + 2) ≤ r + 2 := pow_padic_le_self (by omega)
  have hS : 2 ^ padicValNat 2 (r ^ 2) ≤ 2 ^ 2 := pow_padic_sq_le hL
  have hX : 2 ^ padicValNat 2 (r ^ 2 * (r + 2)) ≤ 2 ^ 2 * (r + 2) :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (by omega) hS hR
  have hY : 2 ^ padicValNat 2 (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) ≤ 2 ^ 2 * (r + 2) * 1 :=
    pow_padic_mul_le (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity)
      hX (pow_padic_le_one hW)
  have hZ : 2 ^ padicValNat 2 ((r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)))
      ≤ 1 * (2 ^ 2 * (r + 2) * 1) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity))
      (pow_padic_le_one hA) hY
  exact le_of_le_of_eq hZ (by ring)

theorem two_SU_A {r : ℕ} (hr : 4 ≤ r) (h4 : r % 4 = 0) :
    2 ^ padicValNat 2 (ordSU (r + 1)) ≤ 4 * r := by
  rw [ordSU_succ]
  have hev : 2 ∣ r := by omega
  have hA : ¬ (2 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hQ : ¬ (2 ∣ r ^ 2 + r + 1) := by
    intro h
    have h1 : 2 ∣ r ^ 2 + r := dvd_add (dvd_pow hev (by norm_num)) hev
    have h2 : 2 ∣ 1 := (Nat.dvd_add_right h1).mp h
    omega
  have hR : 2 ^ padicValNat 2 (r + 2) ≤ 2 := by
    apply pow_padic_le_of_not_sq
    intro h4'
    norm_num at h4'
    omega
  have hL : 2 ^ padicValNat 2 r ≤ r := pow_padic_le_self (by omega)
  have hS : 2 ^ padicValNat 2 ((r + 2) ^ 2) ≤ 2 ^ 2 := pow_padic_sq_le hR
  have hQ' : 2 ^ padicValNat 2 (r ^ 2 + r + 1) ≤ 1 := pow_padic_le_one hQ
  have hX2 : 2 ^ padicValNat 2 (r * (r ^ 2 + r + 1)) ≤ r * 1 :=
    pow_padic_mul_le (by omega) (by positivity) hL hQ'
  have hX1 : 2 ^ padicValNat 2 ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) ≤ 2 ^ 2 * (r * 1) :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)) hS hX2
  have hZ : 2 ^ padicValNat 2 ((r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))))
      ≤ 1 * (2 ^ 2 * (r * 1)) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)))
      (pow_padic_le_one hA) hX1
  exact le_of_le_of_eq hZ (by ring)

theorem two_SU_B {r : ℕ} (hr : 4 ≤ r) (h4 : r % 4 = 2) :
    2 ^ padicValNat 2 (ordSU (r + 1)) ≤ 2 * (r + 2) ^ 2 := by
  rw [ordSU_succ]
  have hev : 2 ∣ r := by omega
  have hA : ¬ (2 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hQ : ¬ (2 ∣ r ^ 2 + r + 1) := by
    intro h
    have h1 : 2 ∣ r ^ 2 + r := dvd_add (dvd_pow hev (by norm_num)) hev
    have h2 : 2 ∣ 1 := (Nat.dvd_add_right h1).mp h
    omega
  have hL : 2 ^ padicValNat 2 r ≤ 2 := by
    apply pow_padic_le_of_not_sq
    intro h4'
    norm_num at h4'
    omega
  have hR : 2 ^ padicValNat 2 (r + 2) ≤ r + 2 := pow_padic_le_self (by omega)
  have hS : 2 ^ padicValNat 2 ((r + 2) ^ 2) ≤ (r + 2) ^ 2 := pow_padic_sq_le hR
  have hQ' : 2 ^ padicValNat 2 (r ^ 2 + r + 1) ≤ 1 := pow_padic_le_one hQ
  have hX2 : 2 ^ padicValNat 2 (r * (r ^ 2 + r + 1)) ≤ 2 * 1 :=
    pow_padic_mul_le (by omega) (by positivity) hL hQ'
  have hX1 : 2 ^ padicValNat 2 ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) ≤ (r + 2) ^ 2 * (2 * 1) :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)) hS hX2
  have hZ : 2 ^ padicValNat 2 ((r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))))
      ≤ 1 * ((r + 2) ^ 2 * (2 * 1)) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)))
      (pow_padic_le_one hA) hX1
  exact le_of_le_of_eq hZ (by ring)

theorem not_nine_dvd_SL (k : ℕ) : ¬ 3 ^ 2 ∣ (3 * k) ^ 2 + 3 * (3 * k) + 3 := by
  intro h
  have e : (3 * k) ^ 2 + 3 * (3 * k) + 3 = 9 * (k ^ 2 + k) + 3 := by ring
  rw [e] at h
  have h9 : 9 ∣ 9 * (k ^ 2 + k) + 3 := h
  generalize k ^ 2 + k = t at h9
  omega

theorem not_nine_dvd_SU (k : ℕ) : ¬ 3 ^ 2 ∣ (3 * k + 1) ^ 2 + (3 * k + 1) + 1 := by
  intro h
  have e : (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 9 * (k ^ 2 + k) + 3 := by ring
  rw [e] at h
  have h9 : 9 ∣ 9 * (k ^ 2 + k) + 3 := h
  generalize k ^ 2 + k = t at h9
  omega

theorem three_SL {r : ℕ} (hr : 4 ≤ r) (h3 : r % 3 = 0) :
    3 ^ padicValNat 3 (ordSL (r + 1)) ≤ 3 * r ^ 2 := by
  rw [ordSL_succ]
  have hA : ¬ (3 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hB : ¬ (3 ∣ r + 2) := by omega
  have hW : ¬ (3 ^ 2 ∣ r ^ 2 + 3 * r + 3) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = 3 * k := ⟨r / 3, by omega⟩
    exact not_nine_dvd_SL k
  have hL : 3 ^ padicValNat 3 r ≤ r := pow_padic_le_self (by omega)
  have hS : 3 ^ padicValNat 3 (r ^ 2) ≤ r ^ 2 := pow_padic_sq_le hL
  have hR : 3 ^ padicValNat 3 (r + 2) ≤ 1 := pow_padic_le_one hB
  have hW' : 3 ^ padicValNat 3 (r ^ 2 + 3 * r + 3) ≤ 3 := pow_padic_le_of_not_sq hW
  have hX : 3 ^ padicValNat 3 (r ^ 2 * (r + 2)) ≤ r ^ 2 * 1 :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (by omega) hS hR
  have hY : 3 ^ padicValNat 3 (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)) ≤ r ^ 2 * 1 * 3 :=
    pow_padic_mul_le (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity) hX hW'
  have hZ : 3 ^ padicValNat 3 ((r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3)))
      ≤ 1 * (r ^ 2 * 1 * 3) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity))
      (pow_padic_le_one hA) hY
  exact le_of_le_of_eq hZ (by ring)

theorem three_SU_a {r : ℕ} (hr : 4 ≤ r) (h3 : r % 3 = 1) (h9 : ¬ 9 ∣ r + 2) :
    3 ^ padicValNat 3 (ordSU (r + 1)) ≤ 27 := by
  rw [ordSU_succ]
  have hA : ¬ (3 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hC : ¬ (3 ∣ r) := by omega
  have hR : 3 ^ padicValNat 3 (r + 2) ≤ 3 := by
    apply pow_padic_le_of_not_sq
    intro h
    exact h9 h
  have hS : 3 ^ padicValNat 3 ((r + 2) ^ 2) ≤ 3 ^ 2 := pow_padic_sq_le hR
  have hQ : ¬ (3 ^ 2 ∣ r ^ 2 + r + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = 3 * k + 1 := ⟨r / 3, by omega⟩
    exact not_nine_dvd_SU k
  have hQ' : 3 ^ padicValNat 3 (r ^ 2 + r + 1) ≤ 3 := pow_padic_le_of_not_sq hQ
  have hL : 3 ^ padicValNat 3 r ≤ 1 := pow_padic_le_one hC
  have hX2 : 3 ^ padicValNat 3 (r * (r ^ 2 + r + 1)) ≤ 1 * 3 :=
    pow_padic_mul_le (by omega) (by positivity) hL hQ'
  have hX1 : 3 ^ padicValNat 3 ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))) ≤ 3 ^ 2 * (1 * 3) :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)) hS hX2
  have hZ : 3 ^ padicValNat 3 ((r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))))
      ≤ 1 * (3 ^ 2 * (1 * 3)) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)))
      (pow_padic_le_one hA) hX1
  exact le_of_le_of_eq hZ (by norm_num)

theorem three_SU_b {r : ℕ} (hr : 4 ≤ r) (h3 : r % 3 = 1) :
    3 ^ padicValNat 3 (ordSU (r + 1)) ≤ 3 * (r + 2) ^ 2 := by
  rw [ordSU_succ]
  have hA : ¬ (3 ∣ (r + 1) ^ 3) := fun h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hC : ¬ (3 ∣ r) := by omega
  have hR : 3 ^ padicValNat 3 (r + 2) ≤ r + 2 := pow_padic_le_self (by omega)
  have hS : 3 ^ padicValNat 3 ((r + 2) ^ 2) ≤ (r + 2) ^ 2 := pow_padic_sq_le hR
  have hQ : ¬ (3 ^ 2 ∣ r ^ 2 + r + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = 3 * k + 1 := ⟨r / 3, by omega⟩
    exact not_nine_dvd_SU k
  have hQ' : 3 ^ padicValNat 3 (r ^ 2 + r + 1) ≤ 3 := pow_padic_le_of_not_sq hQ
  have hL : 3 ^ padicValNat 3 r ≤ 1 := pow_padic_le_one hC
  have hX2 : 3 ^ padicValNat 3 (r * (r ^ 2 + r + 1)) ≤ 1 * 3 :=
    pow_padic_mul_le (by omega) (by positivity) hL hQ'
  have hX1 : 3 ^ padicValNat 3 ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1)))
      ≤ (r + 2) ^ 2 * (1 * 3) :=
    pow_padic_mul_le (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)) hS hX2
  have hZ : 3 ^ padicValNat 3 ((r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1))))
      ≤ 1 * ((r + 2) ^ 2 * (1 * 3)) :=
    pow_padic_mul_le (pow_ne_zero 3 (by omega))
      (mul_ne_zero (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)))
      (pow_padic_le_one hA) hX1
  exact le_of_le_of_eq hZ (by ring)

theorem ordSL_succ_ne_zero {r : ℕ} (hr : 4 ≤ r) : ordSL (r + 1) ≠ 0 := by
  rw [ordSL_succ]
  exact mul_ne_zero (pow_ne_zero 3 (by omega))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by positivity))

theorem ordSU_succ_ne_zero {r : ℕ} (hr : 4 ≤ r) : ordSU (r + 1) ≠ 0 := by
  rw [ordSU_succ]
  exact mul_ne_zero (pow_ne_zero 3 (by omega))
    (mul_ne_zero (pow_ne_zero 2 (by omega)) (mul_ne_zero (by omega) (by positivity)))

theorem cube_two_SL {N c r : ℕ} (hr : 4 ≤ r) (hev : r % 2 = 0) (hc : c = 1 ∨ c = 3)
    (hN : N ≠ 0) (hM : N * c = ordSL (r + 1)) : 2 ^ (3 * padicValNat 2 N) ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (show r % 4 = 0 ∨ r % 4 = 2 by omega) with h4 | h4
  · exact cube_val_le_of_mul hc hN hM (two_SL_A hr h4) (by rw [ordSL_succ]; exact poly_SL_A hr)
  · exact cube_val_le_of_mul hc hN hM (two_SL_B hr h4) (by rw [ordSL_succ]; exact poly_SL_B hr)

theorem cube_two_SU {N c r : ℕ} (hr : 4 ≤ r) (hev : r % 2 = 0) (h3 : r % 3 = 1)
    (hc : c = 1 ∨ c = 3) (hN : N ≠ 0) (hM : N * c = ordSU (r + 1)) :
    2 ^ (3 * padicValNat 2 N) ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (show r % 4 = 0 ∨ r % 4 = 2 by omega) with h4 | h4
  · exact cube_val_le_of_mul hc hN hM (two_SU_A hr h4) (by rw [ordSU_succ]; exact poly_SU_A hr)
  · exact cube_val_le_of_mul hc hN hM (two_SU_B hr h4)
      (by rw [ordSU_succ]; exact poly_SU_B (by omega))

theorem cube_three_SL {N c r : ℕ} (hr : 4 ≤ r) (h3 : r % 3 = 0) (hc : c = 1 ∨ c = 3)
    (hN : N ≠ 0) (hM : N * c = ordSL (r + 1)) : 3 ^ (3 * padicValNat 3 N) ≤ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact cube_val_le_of_mul hc hN hM (three_SL hr h3) (by rw [ordSL_succ]; exact poly_SL_C hr)

theorem cube_three_SU {N c r : ℕ} (hr : 4 ≤ r) (h3 : r % 3 = 1) (hne : r ≠ 7)
    (hc : c = 1 ∨ c = 3) (hN : N ≠ 0) (hM : N * c = ordSU (r + 1)) :
    3 ^ (3 * padicValNat 3 N) ≤ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h9 : 9 ∣ r + 2
  · exact cube_val_le_of_mul hc hN hM (three_SU_b hr h3)
      (by rw [ordSU_succ]; exact poly_SU_D (by omega))
  · exact cube_val_le_of_mul hc hN hM (three_SU_a hr h3 h9)
      (by rw [ordSU_succ]; exact poly_SU_C hr)

theorem A1_a_SL {p e N c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hc : c = 1 ∨ c = 3) (hM : N * c = ordSL (p ^ e)) : padicValNat p N = 3 * e := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact padicValNat_ordSL h5 he hc hM

theorem A1_a_SU {p e N c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hc : c = 1 ∨ c = 3) (hM : N * c = ordSU (p ^ e)) : padicValNat p N = 3 * e := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact padicValNat_ordSU h5 he hc hM

theorem A1_c_SL {p e N c l : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hmod : p ^ e % 3 = 1) (hc : c = 1 ∨ c = 3) (hM : N * c = ordSL (p ^ e))
    (hl : l.Prime) (hlp : l ≠ p) : l ^ (3 * padicValNat l N) ≤ N := by
  have hpe : p ≤ p ^ e := le_self_pow (by omega) (by omega)
  obtain ⟨r, hr⟩ : ∃ r, p ^ e = r + 1 := ⟨p ^ e - 1, by omega⟩
  have hr4 : 4 ≤ r := by omega
  have hp2 : p % 2 = 1 := by rcases hp.eq_two_or_odd with h | h <;> omega
  have hodd : p ^ e % 2 = 1 := by rw [Nat.pow_mod, hp2]; simp
  have hev : r % 2 = 0 := by omega
  have h3 : r % 3 = 0 := by omega
  rw [hr] at hM
  have hN : N ≠ 0 := by
    intro h0
    apply ordSL_succ_ne_zero hr4
    rw [← hM, h0, zero_mul]
  have hl3 : l = 2 ∨ l = 3 ∨ 5 ≤ l := by
    have := hl.two_le
    rcases Nat.lt_or_ge l 5 with h | h
    · interval_cases l
      · omega
      · omega
      · exfalso
        have h24 := hl.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩
        omega
    · exact Or.inr (Or.inr h)
  rcases hl3 with rfl | rfl | h5l
  · exact cube_two_SL hr4 hev hc hN hM
  · exact cube_three_SL hr4 h3 hc hN hM
  · haveI : Fact l.Prime := ⟨hl⟩
    have hlq : ¬ l ∣ r + 1 := by
      intro h
      rw [← hr] at h
      exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h))
    exact cube_val_le_SL h5l hr4 hc hlq hM

theorem A1_c_SU {p e N c l : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hmod : p ^ e % 3 = 2) (hc : c = 1 ∨ c = 3) (hM : N * c = ordSU (p ^ e))
    (hl : l.Prime) (hlp : l ≠ p) : l ^ (3 * padicValNat l N) ≤ N := by
  have hpe : p ≤ p ^ e := le_self_pow (by omega) (by omega)
  obtain ⟨r, hr⟩ : ∃ r, p ^ e = r + 1 := ⟨p ^ e - 1, by omega⟩
  have hr4 : 4 ≤ r := by omega
  have hp2 : p % 2 = 1 := by rcases hp.eq_two_or_odd with h | h <;> omega
  have hodd : p ^ e % 2 = 1 := by rw [Nat.pow_mod, hp2]; simp
  have hev : r % 2 = 0 := by omega
  have h3 : r % 3 = 1 := by omega
  have hne : r ≠ 7 := by
    intro h7
    have h8 : p ^ e = 8 := by omega
    have hpd : p ∣ 8 := by
      rw [← h8]
      exact dvd_pow_self p (by omega)
    have hle : p ≤ 8 := Nat.le_of_dvd (by norm_num) hpd
    interval_cases p <;> first | omega | (have h2 := hp.eq_one_or_self_of_dvd 2 ⟨4, rfl⟩; omega)
  rw [hr] at hM
  have hN : N ≠ 0 := by
    intro h0
    apply ordSU_succ_ne_zero hr4
    rw [← hM, h0, zero_mul]
  have hl3 : l = 2 ∨ l = 3 ∨ 5 ≤ l := by
    have := hl.two_le
    rcases Nat.lt_or_ge l 5 with h | h
    · interval_cases l
      · omega
      · omega
      · exfalso
        have h24 := hl.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩
        omega
    · exact Or.inr (Or.inr h)
  rcases hl3 with rfl | rfl | h5l
  · exact cube_two_SU hr4 hev h3 hc hN hM
  · exact cube_three_SU hr4 h3 hne hc hN hM
  · haveI : Fact l.Prime := ⟨hl⟩
    have hlq : ¬ l ∣ r + 1 := by
      intro h
      rw [← hr] at h
      exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h))
    exact cube_val_le_SU h5l hr4 hc hlq hM

end Arith

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

end
