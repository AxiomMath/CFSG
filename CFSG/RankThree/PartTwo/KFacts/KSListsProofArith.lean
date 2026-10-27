module

public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec11.KSListsProof

open CFSG.Open (ordTrialityD4 ordG2)

theorem dvd_of_dvd_add_left {r a d : ℕ} (ha : r ∣ a) (had : r ∣ a + d) : r ∣ d :=
  (Nat.dvd_add_right ha).mp had

theorem coprime_pow_of_not_dvd {r k n : ℕ} (hr : r.Prime) (hn : ¬ r ∣ n) :
    Nat.Coprime (r ^ k) n :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).mpr hn)

theorem eq_two_of_dvd_two {r : ℕ} (hr : r.Prime) (h : r ∣ 2) : r = 2 :=
  (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h

theorem not_dvd_one_of_prime {r : ℕ} (hr : r.Prime) : ¬ r ∣ 1 := fun h =>
  hr.one_lt.ne' (Nat.dvd_one.mp h)

theorem pow_le_succ_of_dvd_consecutive {r k a : ℕ} (hr : r.Prime) (hra : r ≠ 2 ∨ 2 ∣ a)
    (ha : 2 ≤ a) (h : r ^ k ∣ (a - 1) * a * (a + 1)) : r ^ k ≤ a + 1 := by
  have e : (a - 1) * a * (a + 1) = a * ((a - 1) * (a + 1)) := by ring
  rw [e] at h
  by_cases h0 : r ∣ a
  · have h1 : ¬ r ∣ a - 1 := fun h1 => not_dvd_one_of_prime hr
      (dvd_of_dvd_add_left h1 (by rwa [show a - 1 + 1 = a by omega]))
    have h2 : ¬ r ∣ a + 1 := fun h2 => not_dvd_one_of_prime hr (dvd_of_dvd_add_left h0 h2)
    have hc : Nat.Coprime (r ^ k) ((a - 1) * (a + 1)) :=
      coprime_pow_of_not_dvd hr fun h3 => ((Nat.Prime.dvd_mul hr).mp h3).elim h1 h2
    exact (Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h)).trans (Nat.le_succ a)
  · have h' : r ^ k ∣ (a - 1) * (a + 1) := (coprime_pow_of_not_dvd hr h0).dvd_of_dvd_mul_left h
    by_cases h1 : r ∣ a - 1
    · have h2 : ¬ r ∣ a + 1 := by
        intro h2
        have hr2 : r = 2 :=
          eq_two_of_dvd_two hr (dvd_of_dvd_add_left h1 (by rwa [show a - 1 + 2 = a + 1 by omega]))
        rcases hra with hra | hra
        · exact hra hr2
        · exact h0 (hr2 ▸ hra)
      exact (Nat.le_of_dvd (by omega)
        ((coprime_pow_of_not_dvd hr h2).dvd_of_dvd_mul_right h')).trans (by omega)
    · exact Nat.le_of_dvd (by omega) ((coprime_pow_of_not_dvd hr h1).dvd_of_dvd_mul_left h')

theorem two_pow_le_of_dvd_mul_succ {a k : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (h : 2 ^ (k + 1) ∣ (a - 1) * (a + 1)) : 2 ^ k ≤ a + 1 := by
  obtain ⟨t, rfl⟩ := ha
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e : (2 * t + 1 - 1) * (2 * t + 1 + 1) = 2 ^ 2 * (t * (t + 1)) := by
    rw [show 2 * t + 1 - 1 = 2 * t by omega]
    ring
  rw [e, show j + 1 + 1 = 2 + j by ring, pow_add] at h
  have hj : 2 ^ j ∣ t * (t + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  rcases Nat.even_or_odd t with hte | hto
  · have hc : Nat.Coprime (2 ^ j) (t + 1) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hte.add_one)
    have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right hj)
    rw [pow_succ]
    omega
  · have hc : Nat.Coprime (2 ^ j) t := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hto)
    have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left hj)
    rw [pow_succ]
    omega

theorem pow_le_of_dvd_three_factors {r k A B C a b : ℕ} (hr : r.Prime) (hA : 0 < A)
    (hB : 0 < B) (hC : 0 < C) (hAB : r ∣ A → ¬ r ∣ B) (hBC : r ∣ B → ¬ r ∣ C)
    (hAC : r ∣ A → r ∣ C → r = 3 ∧ ¬ 9 ∣ C) (h : r ^ k ∣ A ^ a * B ^ b * C) :
    r ^ k ≤ 3 * A ^ a ∨ r ^ k ≤ B ^ b ∨ r ^ k ≤ C := by
  have hpow : ∀ {n m : ℕ}, ¬ r ∣ n → ¬ r ∣ n ^ m := fun hn hnm => hn (hr.dvd_of_dvd_pow hnm)
  have e : A ^ a * B ^ b * C = B ^ b * (A ^ a * C) := by ring
  rw [e] at h
  by_cases hrB : r ∣ B
  · have hrA : ¬ r ∣ A := fun hrA => hAB hrA hrB
    have hrC : ¬ r ∣ C := hBC hrB
    have hc : Nat.Coprime (r ^ k) (A ^ a * C) :=
      Nat.Coprime.mul_right (coprime_pow_of_not_dvd hr (hpow hrA)) (coprime_pow_of_not_dvd hr hrC)
    exact Or.inr (Or.inl (Nat.le_of_dvd (pow_pos hB b) (hc.dvd_of_dvd_mul_right h)))
  · have h' : r ^ k ∣ A ^ a * C := (coprime_pow_of_not_dvd hr (hpow hrB)).dvd_of_dvd_mul_left h
    by_cases hrA : r ∣ A
    · by_cases hrC : r ∣ C
      · obtain ⟨rfl, h9⟩ := hAC hrA hrC
        obtain ⟨C', rfl⟩ := hrC
        have h3 : ¬ 3 ∣ C' := fun h3 => h9 (by
          obtain ⟨c, rfl⟩ := h3
          exact ⟨c, by ring⟩)
        have h'' : 3 ^ k ∣ (3 * A ^ a) * C' := by
          have : A ^ a * (3 * C') = (3 * A ^ a) * C' := by ring
          rwa [this] at h'
        exact Or.inl (Nat.le_of_dvd (by positivity)
          ((coprime_pow_of_not_dvd hr h3).dvd_of_dvd_mul_right h''))
      · exact Or.inl ((Nat.le_of_dvd (pow_pos hA a)
          ((coprime_pow_of_not_dvd hr hrC).dvd_of_dvd_mul_right h')).trans
          (Nat.le_mul_of_pos_left _ (by norm_num)))
    · exact Or.inr (Or.inr (Nat.le_of_dvd hC
        ((coprime_pow_of_not_dvd hr (hpow hrA)).dvd_of_dvd_mul_left h')))

theorem sl3_factor {x : ℕ} (hx : 1 ≤ x) :
    (x ^ 2 - 1) * (x ^ 3 - 1) = (x - 1) ^ 2 * (x + 1) ^ 1 * (x ^ 2 + x + 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [hx, h2, h3]
  ring

theorem su3_factor {x : ℕ} (hx : 1 ≤ x) :
    (x ^ 2 - 1) * (x ^ 3 + 1) = (x + 1) ^ 2 * (x - 1) ^ 1 * (x ^ 2 - x + 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : x ≤ x ^ 2 := by nlinarith
  zify [hx, h2, h3]
  ring

theorem sl3_conditions {r x : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hx : 2 ≤ x) :
    (r ∣ x - 1 → ¬ r ∣ x + 1) ∧ (r ∣ x + 1 → ¬ r ∣ x ^ 2 + x + 1) ∧
      (r ∣ x - 1 → r ∣ x ^ 2 + x + 1 → r = 3 ∧ ¬ 9 ∣ x ^ 2 + x + 1) := by
  refine ⟨fun hA hB => hr2 (eq_two_of_dvd_two hr
    (dvd_of_dvd_add_left hA (by rwa [show x - 1 + 2 = x + 1 by omega]))), fun hB hC => ?_,
    fun hA hC => ?_⟩
  · have e : x ^ 2 + x + 1 = (x + 1) * x + 1 := by ring
    rw [e] at hC
    exact not_dvd_one_of_prime hr (dvd_of_dvd_add_left (Dvd.dvd.mul_right hB x) hC)
  · have e : x ^ 2 + x + 1 = (x - 1) * (x + 2) + 3 := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    have h3 : r ∣ 3 := by
      rw [e] at hC
      exact dvd_of_dvd_add_left (Dvd.dvd.mul_right hA _) hC
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    subst hr3
    refine ⟨rfl, ?_⟩
    obtain ⟨t, ht⟩ := hA
    obtain rfl : x = 3 * t + 1 := by omega
    have e' : (3 * t + 1) ^ 2 + (3 * t + 1) + 1 = 9 * (t ^ 2 + t) + 3 := by ring
    rw [e']
    omega

theorem su3_conditions {r x : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hx : 2 ≤ x) :
    (r ∣ x + 1 → ¬ r ∣ x - 1) ∧ (r ∣ x - 1 → ¬ r ∣ x ^ 2 - x + 1) ∧
      (r ∣ x + 1 → r ∣ x ^ 2 - x + 1 → r = 3 ∧ ¬ 9 ∣ x ^ 2 - x + 1) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
  have e1 : (y + 2) ^ 2 - (y + 2) + 1 = (y + 1) * (y + 2) + 1 := by
    have : (y + 2) ^ 2 = (y + 1) * (y + 2) + (y + 2) := by ring
    omega
  have e2 : (y + 2) ^ 2 - (y + 2) + 1 = (y + 2 + 1) * y + 3 := by
    have : (y + 2) ^ 2 = (y + 2 + 1) * y + 3 + (y + 2) - 1 := by
      have : (y + 2 + 1) * y + 3 + (y + 2) = (y + 2) ^ 2 + 1 := by ring
      omega
    omega
  have hsub : y + 2 - 1 = y + 1 := by omega
  rw [hsub]
  refine ⟨fun hA hB => hr2 (eq_two_of_dvd_two hr
    (dvd_of_dvd_add_left hB (by rwa [show y + 1 + 2 = y + 2 + 1 by omega]))), fun hB hC => ?_,
    fun hA hC => ?_⟩
  · rw [e1] at hC
    exact not_dvd_one_of_prime hr (dvd_of_dvd_add_left (Dvd.dvd.mul_right hB _) hC)
  · have h3 : r ∣ 3 := by
      rw [e2] at hC
      exact dvd_of_dvd_add_left (Dvd.dvd.mul_right hA _) hC
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    subst hr3
    refine ⟨rfl, ?_⟩
    obtain ⟨t, rfl⟩ : 3 ∣ y := by omega
    rw [e1, show (3 * t + 1) * (3 * t + 2) + 1 = 9 * (t ^ 2 + t) + 3 by ring]
    omega

theorem pow_le_of_dvd_sl3 {r k x : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hx : 2 ≤ x)
    (h : r ^ k ∣ (x ^ 2 - 1) * (x ^ 3 - 1)) : r ^ k ≤ 3 * (x + 1) ^ 2 := by
  rw [sl3_factor (by omega)] at h
  obtain ⟨hAB, hBC, hAC⟩ := sl3_conditions hr hr2 hx
  rcases pow_le_of_dvd_three_factors hr (by omega) (by omega) (by positivity) hAB hBC hAC h with
    h1 | h1 | h1
  · exact h1.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2))
  · refine h1.trans ?_
    rw [pow_one]
    nlinarith
  · exact h1.trans (by nlinarith)

theorem pow_le_of_dvd_su3 {r k x : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hx : 2 ≤ x)
    (h : r ^ k ∣ (x ^ 2 - 1) * (x ^ 3 + 1)) : r ^ k ≤ 3 * (x + 1) ^ 2 := by
  rw [su3_factor (by omega)] at h
  obtain ⟨hAB, hBC, hAC⟩ := su3_conditions hr hr2 hx
  have hC : 0 < x ^ 2 - x + 1 := by omega
  rcases pow_le_of_dvd_three_factors hr (by omega) (by omega) hC hAB hBC hAC h with h1 | h1 | h1
  · exact h1
  · refine h1.trans ?_
    rw [pow_one]
    have : x - 1 ≤ x + 1 := by omega
    nlinarith
  · refine h1.trans ?_
    have : x ^ 2 - x + 1 ≤ x ^ 2 + 1 := by omega
    nlinarith

theorem g2_factor {p : ℕ} (hp : 1 ≤ p) :
    (p ^ 6 - 1) * (p ^ 2 - 1) = (p ^ 3 + 1) * ((p ^ 2 - 1) * (p ^ 3 - 1)) ∧
      (p ^ 6 - 1) * (p ^ 2 - 1) = (p ^ 3 - 1) * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ p ^ 6 := Nat.one_le_pow _ _ (by omega)
  constructor <;> (zify [h2, h3, h6]; ring)

theorem pow_le_of_dvd_g2 {r k p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 2 ≤ p)
    (h : r ^ k ∣ (p ^ 6 - 1) * (p ^ 2 - 1)) : r ^ k ≤ 3 * (p + 1) ^ 2 := by
  obtain ⟨e1, e2⟩ := g2_factor (p := p) (by omega)
  have h3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  by_cases h1 : r ∣ p ^ 3 + 1
  · have h2 : ¬ r ∣ p ^ 3 - 1 := fun h2 => hr2 (eq_two_of_dvd_two hr
      (dvd_of_dvd_add_left h2 (by rwa [show p ^ 3 - 1 + 2 = p ^ 3 + 1 by omega])))
    rw [e2] at h
    exact pow_le_of_dvd_su3 hr hr2 hp ((coprime_pow_of_not_dvd hr h2).dvd_of_dvd_mul_left h)
  · rw [e1] at h
    exact pow_le_of_dvd_sl3 hr hr2 hp ((coprime_pow_of_not_dvd hr h1).dvd_of_dvd_mul_left h)

theorem pow_le_of_dvd_sp4 {r k p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 2 ≤ p)
    (h : r ^ k ∣ (p ^ 2 - 1) * (p ^ 4 - 1)) : r ^ k ≤ 3 * (p + 1) ^ 2 := by
  have e : (p ^ 2 - 1) * (p ^ 4 - 1) = (p - 1) ^ 2 * (p + 1) ^ 2 * (p ^ 2 + 1) := by
    have h1 : 1 ≤ p := by omega
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h4 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2, h4]
    ring
  rw [e] at h
  have eC : p ^ 2 + 1 = (p - 1) * (p + 1) + 2 := by
    obtain ⟨y, rfl⟩ : ∃ y, p = y + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hAB : r ∣ p - 1 → ¬ r ∣ p + 1 := fun hA hB => hr2 (eq_two_of_dvd_two hr
    (dvd_of_dvd_add_left hA (by rwa [show p - 1 + 2 = p + 1 by omega])))
  have hBC : r ∣ p + 1 → ¬ r ∣ p ^ 2 + 1 := fun hB hC => hr2 (eq_two_of_dvd_two hr
    (dvd_of_dvd_add_left (Dvd.dvd.mul_left hB _) (by rwa [← eC])))
  have hAC : r ∣ p - 1 → r ∣ p ^ 2 + 1 → r = 3 ∧ ¬ 9 ∣ p ^ 2 + 1 := fun hA hC =>
    absurd (eq_two_of_dvd_two hr (dvd_of_dvd_add_left (Dvd.dvd.mul_right hA _) (by rwa [← eC])))
      hr2
  rcases pow_le_of_dvd_three_factors hr (by omega) (by omega) (by positivity) hAB hBC hAC h with
    h1 | h1 | h1
  · exact h1.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2))
  · exact h1.trans (by nlinarith)
  · exact h1.trans (by nlinarith)

theorem l4_factor {p : ℕ} (hp : 1 ≤ p) :
    (p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1) =
      (p - 1) ^ 3 * (p + 1) ^ 2 * (p ^ 2 + p + 1) * (p ^ 2 + 1) := by
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [hp, h2, h3, h4]
  ring

theorem u4_factor {p : ℕ} (hp : 1 ≤ p) :
    (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) =
      (p + 1) ^ 3 * (p - 1) ^ 2 * (p ^ 2 - p + 1) * (p ^ 2 + 1) := by
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2' : p ≤ p ^ 2 := by nlinarith
  have h4 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [hp, h2, h2', h4]
  ring

theorem not_dvd_of_dvd_sq_add_one {r p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 2 ≤ p)
    (hD : r ∣ p ^ 2 + 1) :
    ¬ r ∣ p - 1 ∧ ¬ r ∣ p + 1 ∧ ¬ r ∣ p ^ 2 + p + 1 ∧ ¬ r ∣ p ^ 2 - p + 1 := by
  have eC : p ^ 2 + 1 = (p - 1) * (p + 1) + 2 := by
    obtain ⟨y, rfl⟩ : ∃ y, p = y + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hrp : ¬ r ∣ p := fun h => not_dvd_one_of_prime hr
    (dvd_of_dvd_add_left (dvd_pow h two_ne_zero) hD)
  refine ⟨fun hA => hr2 (eq_two_of_dvd_two hr
      (dvd_of_dvd_add_left (Dvd.dvd.mul_right hA _) (by rwa [← eC]))),
    fun hB => hr2 (eq_two_of_dvd_two hr
      (dvd_of_dvd_add_left (Dvd.dvd.mul_left hB _) (by rwa [← eC]))),
    fun hC => hrp (dvd_of_dvd_add_left hD (by rwa [show p ^ 2 + 1 + p = p ^ 2 + p + 1 by ring])),
    fun hC => hrp (dvd_of_dvd_add_left hC ?_)⟩
  have : p ≤ p ^ 2 := by nlinarith
  rwa [show p ^ 2 - p + 1 + p = p ^ 2 + 1 by omega]

theorem pow_le_of_dvd_l4 {r k p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 2 ≤ p)
    (h : r ^ k ∣ (p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1)) : r ^ k ≤ 3 * (p + 1) ^ 3 := by
  rw [l4_factor (by omega)] at h
  by_cases hD : r ∣ p ^ 2 + 1
  · obtain ⟨hA, hB, hC, -⟩ := not_dvd_of_dvd_sq_add_one hr hr2 hp hD
    have hc : Nat.Coprime (r ^ k) ((p - 1) ^ 3 * (p + 1) ^ 2 * (p ^ 2 + p + 1)) := by
      refine coprime_pow_of_not_dvd hr fun h' => ?_
      rcases (Nat.Prime.dvd_mul hr).mp h' with h' | h'
      · rcases (Nat.Prime.dvd_mul hr).mp h' with h' | h'
        · exact hA (hr.dvd_of_dvd_pow h')
        · exact hB (hr.dvd_of_dvd_pow h')
      · exact hC h'
    exact (Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_left h)).trans (by nlinarith)
  · have h' := (coprime_pow_of_not_dvd hr hD).dvd_of_dvd_mul_right h
    obtain ⟨hAB, hBC, hAC⟩ := sl3_conditions hr hr2 hp
    rcases pow_le_of_dvd_three_factors hr (by omega) (by omega) (by positivity) hAB hBC hAC h' with
      h1 | h1 | h1
    · exact h1.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 3))
    · exact h1.trans (by nlinarith)
    · exact h1.trans (by nlinarith)

theorem pow_le_of_dvd_u4 {r k p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 2 ≤ p)
    (h : r ^ k ∣ (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1)) : r ^ k ≤ 3 * (p + 1) ^ 3 := by
  rw [u4_factor (by omega)] at h
  have hC0 : 0 < p ^ 2 - p + 1 := by omega
  by_cases hD : r ∣ p ^ 2 + 1
  · obtain ⟨hA, hB, -, hC⟩ := not_dvd_of_dvd_sq_add_one hr hr2 hp hD
    have hc : Nat.Coprime (r ^ k) ((p + 1) ^ 3 * (p - 1) ^ 2 * (p ^ 2 - p + 1)) := by
      refine coprime_pow_of_not_dvd hr fun h' => ?_
      rcases (Nat.Prime.dvd_mul hr).mp h' with h' | h'
      · rcases (Nat.Prime.dvd_mul hr).mp h' with h' | h'
        · exact hB (hr.dvd_of_dvd_pow h')
        · exact hA (hr.dvd_of_dvd_pow h')
      · exact hC h'
    exact (Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_left h)).trans (by nlinarith)
  · have h' := (coprime_pow_of_not_dvd hr hD).dvd_of_dvd_mul_right h
    obtain ⟨hAB, hBC, hAC⟩ := su3_conditions hr hr2 hp
    rcases pow_le_of_dvd_three_factors hr (by omega) (by omega) hC0 hAB hBC hAC h' with
      h1 | h1 | h1
    · exact h1
    · refine h1.trans ?_
      have : (p - 1) ^ 2 ≤ (p + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
    · refine h1.trans ?_
      have : p ^ 2 - p + 1 ≤ p ^ 2 + 1 := by omega
      nlinarith

theorem dvd_of_pow_twelve_dvd {r f p a N : ℕ} (hr : r.Prime) (hp : p.Prime) (hf : 1 ≤ f)
    (ha : a < 12) (hpN : ¬ p ∣ N) (h : (r ^ f) ^ 12 ∣ p ^ a * N) : (r ^ f) ^ 12 ∣ N := by
  by_cases hrp : r = p
  · subst hrp
    exfalso
    rw [← pow_mul] at h
    have h1 : r ^ (f * 12) ∣ r ^ a := (coprime_pow_of_not_dvd hr hpN).dvd_of_dvd_mul_right h
    have := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).mp h1
    omega
  · have hc : Nat.Coprime ((r ^ f) ^ 12) (p ^ a) :=
      Nat.Coprime.pow 12 a (Nat.Coprime.pow_left f ((Nat.coprime_primes hr hp).mpr hrp))
    exact hc.dvd_of_dvd_mul_left h

theorem not_dvd_pow_sub_one {p x k : ℕ} (hp : p.Prime) (hx : p ∣ x) (hx1 : 1 ≤ x) (hk : 1 ≤ k) :
    ¬ p ∣ x ^ k - 1 := fun h => not_dvd_one_of_prime hp (dvd_of_dvd_add_left h
  (by rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]; exact dvd_pow hx (by omega)))

theorem not_dvd_pow_add_one {p x k : ℕ} (hp : p.Prime) (hx : p ∣ x) (hk : 1 ≤ k) :
    ¬ p ∣ x ^ k + 1 := fun h => not_dvd_one_of_prime hp
  (dvd_of_dvd_add_left (dvd_pow hx (by omega)) h)

theorem pow_le_pow_sub_one {x : ℕ} (hx : 2 ≤ x) {k l : ℕ} (hkl : k < l) : x ^ k ≤ x ^ l - 1 := by
  have h1 : 2 * x ^ k ≤ x ^ (k + 1) := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ hx
  have h2 : x ^ (k + 1) ≤ x ^ l := Nat.pow_le_pow_right (by omega) hkl
  have : 1 ≤ x ^ k := Nat.one_le_pow _ _ (by omega)
  omega

theorem ordTrialityD4_lt_pow {q : ℕ} (hq : 2 ≤ q) : ordTrialityD4 q < q ^ 28 := by
  have h1 : (q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1) < q ^ 10 := by
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h2]
    have e : (q : ℤ) ^ 10 - ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 2 - 1) =
        (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) + (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) + 1 := by ring
    have hq2 : (1 : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast h2
    have : 0 ≤ (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) := mul_nonneg (by positivity) (by linarith)
    have : 0 ≤ (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  have h6 : q ^ 6 - 1 < q ^ 6 := Nat.sub_lt (by positivity) one_pos
  unfold ordTrialityD4
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      = q ^ 12 * (((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)) * (q ^ 6 - 1)) := by ring
    _ < q ^ 12 * (q ^ 10 * q ^ 6) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' h1 h6) (by positivity)
    _ = q ^ 28 := by ring

theorem pow_twelve_dvd_ordTrialityD4 (q : ℕ) : q ^ 12 ∣ ordTrialityD4 q :=
  ⟨(q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1), by unfold ordTrialityD4; ring⟩

theorem ordG2_lt_pow {q : ℕ} (hq : 2 ≤ q) : ordG2 q < q ^ 14 := by
  unfold ordG2
  have h6 : q ^ 6 - 1 < q ^ 6 := Nat.sub_lt (by positivity) one_pos
  have h2 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (by positivity) one_pos
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) = q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by ring
    _ < q ^ 6 * (q ^ 6 * q ^ 2) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' h6 h2) (by positivity)
    _ = q ^ 14 := by ring

theorem pow_le_ordG2 {q : ℕ} (hq : 2 ≤ q) : q ^ 12 ≤ ordG2 q := by
  unfold ordG2
  have h6 := pow_le_pow_sub_one hq (show 5 < 6 by norm_num)
  have h2 := pow_le_pow_sub_one hq (show 1 < 2 by norm_num)
  calc q ^ 12 = q ^ 6 * (q ^ 5 * q ^ 1) := by ring
    _ ≤ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h6 h2)
    _ = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by ring

theorem pow_five_le {Q x : ℕ} (hQ : 3 ≤ Q) (h : Q ^ 12 ≤ 3 * (x + 1) ^ 2) : Q ^ 5 ≤ x := by
  by_contra hlt
  push Not at hlt
  have h1 : (x + 1) ^ 2 ≤ (Q ^ 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h9 : 9 ≤ Q ^ 2 := by nlinarith
  have h2 : 3 * (Q ^ 5) ^ 2 < Q ^ 12 := by
    have hpos : 0 < (Q ^ 5) ^ 2 := by positivity
    calc 3 * (Q ^ 5) ^ 2 < 9 * (Q ^ 5) ^ 2 := by omega
      _ ≤ Q ^ 2 * (Q ^ 5) ^ 2 := Nat.mul_le_mul_right _ h9
      _ = Q ^ 12 := by ring
  omega

theorem pow_three_le {Q x : ℕ} (hQ : 3 ≤ Q) (h : Q ^ 12 ≤ 3 * (x + 1) ^ 3) : Q ^ 3 ≤ x := by
  by_contra hlt
  push Not at hlt
  have h1 : (x + 1) ^ 3 ≤ (Q ^ 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h27 : 27 ≤ Q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h2 : 3 * (Q ^ 3) ^ 3 < Q ^ 12 := by
    have hpos : 0 < (Q ^ 3) ^ 3 := by positivity
    calc 3 * (Q ^ 3) ^ 3 < 27 * (Q ^ 3) ^ 3 := by omega
      _ ≤ Q ^ 3 * (Q ^ 3) ^ 3 := Nat.mul_le_mul_right _ h27
      _ = Q ^ 12 := by ring
  omega

theorem lt_psl2 {Q x : ℕ} (hQ : 2 ≤ Q) (hx : Q ^ 12 ≤ x + 1) :
    2 * ordTrialityD4 Q < x * (x ^ 2 - 1) := by
  have h11 : Q ^ 11 ≤ x := by
    have := pow_le_pow_sub_one hQ (show 11 < 12 by norm_num)
    omega
  have h21 : Q ^ 21 ≤ x ^ 2 - 1 := by
    have h1 := pow_le_pow_sub_one hQ (show 21 < 22 by norm_num)
    have h2 : Q ^ 22 ≤ x ^ 2 := by
      calc Q ^ 22 = (Q ^ 11) ^ 2 := by ring
        _ ≤ x ^ 2 := Nat.pow_le_pow_left h11 2
    omega
  have h16 : 16 ≤ Q ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ Q ^ 4 := Nat.pow_le_pow_left hQ 4
  calc 2 * ordTrialityD4 Q < 2 * Q ^ 28 :=
        Nat.mul_lt_mul_of_pos_left (ordTrialityD4_lt_pow hQ) (by norm_num)
    _ ≤ Q ^ 4 * Q ^ 28 := Nat.mul_le_mul_right _ (by omega)
    _ = Q ^ 11 * Q ^ 21 := by ring
    _ ≤ x * (x ^ 2 - 1) := Nat.mul_le_mul h11 h21

theorem lt_sl3 {Q x : ℕ} (hQ : 3 ≤ Q) (hx : Q ^ 12 ≤ 3 * (x + 1) ^ 2) :
    3 * ordTrialityD4 Q < x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := by
  have h5 := pow_five_le hQ hx
  have hQ2 : 2 ≤ Q := by omega
  have hx3 : Q ^ 15 ≤ x ^ 3 := by
    calc Q ^ 15 = (Q ^ 5) ^ 3 := by ring
      _ ≤ x ^ 3 := Nat.pow_le_pow_left h5 3
  have hx2 : Q ^ 9 ≤ x ^ 2 - 1 := by
    have h1 := pow_le_pow_sub_one hQ2 (show 9 < 10 by norm_num)
    have h2 : Q ^ 10 ≤ x ^ 2 := by
      calc Q ^ 10 = (Q ^ 5) ^ 2 := by ring
        _ ≤ x ^ 2 := Nat.pow_le_pow_left h5 2
    omega
  have hx3' : Q ^ 14 ≤ x ^ 3 - 1 := by
    have h1 := pow_le_pow_sub_one hQ2 (show 14 < 15 by norm_num)
    omega
  have h10 : 3 ≤ Q ^ 10 := by
    calc 3 ≤ Q := hQ
      _ ≤ Q ^ 10 := Nat.le_self_pow (by norm_num) Q
  calc 3 * ordTrialityD4 Q < 3 * Q ^ 28 :=
        Nat.mul_lt_mul_of_pos_left (ordTrialityD4_lt_pow hQ2) (by norm_num)
    _ ≤ Q ^ 10 * Q ^ 28 := Nat.mul_le_mul_right _ h10
    _ = Q ^ 15 * (Q ^ 9 * Q ^ 14) := by ring
    _ ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) :=
        Nat.mul_le_mul hx3 (Nat.mul_le_mul hx2 hx3')

theorem lt_g2 {Q p : ℕ} (hQ : 3 ≤ Q) (hp : Q ^ 12 ≤ 3 * (p + 1) ^ 2) :
    ordTrialityD4 Q < ordG2 p := by
  have h5 := pow_five_le hQ hp
  have hQ2 : 2 ≤ Q := by omega
  have hp2 : 2 ≤ p := le_trans (by nlinarith [Nat.one_le_pow 4 Q (by omega)]) h5
  calc ordTrialityD4 Q < Q ^ 28 := ordTrialityD4_lt_pow hQ2
    _ ≤ Q ^ 60 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ = (Q ^ 5) ^ 12 := by ring
    _ ≤ p ^ 12 := Nat.pow_le_pow_left h5 12
    _ ≤ ordG2 p := pow_le_ordG2 hp2

theorem lt_sp4 {Q p : ℕ} (hQ : 3 ≤ Q) (hp : Q ^ 12 ≤ 3 * (p + 1) ^ 2) :
    2 * ordTrialityD4 Q < p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
  have h5 := pow_five_le hQ hp
  have hQ2 : 2 ≤ Q := by omega
  have hp2 : 2 ≤ p := le_trans (by nlinarith [Nat.one_le_pow 4 Q (by omega)]) h5
  have hp4 : Q ^ 20 ≤ p ^ 4 := by
    calc Q ^ 20 = (Q ^ 5) ^ 4 := by ring
      _ ≤ p ^ 4 := Nat.pow_le_pow_left h5 4
  have hp21 : Q ^ 5 ≤ p ^ 2 - 1 := le_trans h5 (by
    have := pow_le_pow_sub_one hp2 (show 1 < 2 by norm_num)
    rwa [pow_one] at this)
  have hp43 : Q ^ 15 ≤ p ^ 4 - 1 := by
    have h1 := pow_le_pow_sub_one hp2 (show 3 < 4 by norm_num)
    have h2 : Q ^ 15 ≤ p ^ 3 := by
      calc Q ^ 15 = (Q ^ 5) ^ 3 := by ring
        _ ≤ p ^ 3 := Nat.pow_le_pow_left h5 3
    omega
  have h12 : 2 ≤ Q ^ 12 := le_trans hQ2 (Nat.le_self_pow (by norm_num) Q)
  calc 2 * ordTrialityD4 Q < 2 * Q ^ 28 :=
        Nat.mul_lt_mul_of_pos_left (ordTrialityD4_lt_pow hQ2) (by norm_num)
    _ ≤ Q ^ 12 * Q ^ 28 := Nat.mul_le_mul_right _ h12
    _ = Q ^ 20 * (Q ^ 5 * Q ^ 15) := by ring
    _ ≤ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := Nat.mul_le_mul hp4 (Nat.mul_le_mul hp21 hp43)

theorem lt_l4 {Q p : ℕ} (hQ : 3 ≤ Q) (hp : Q ^ 12 ≤ 3 * (p + 1) ^ 3) :
    4 * ordTrialityD4 Q < p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1)) := by
  have h3 := pow_three_le hQ hp
  have hQ2 : 2 ≤ Q := by omega
  have hp2 : 2 ≤ p := le_trans (by nlinarith [Nat.one_le_pow 2 Q (by omega)]) h3
  have hp6 : Q ^ 18 ≤ p ^ 6 := by
    calc Q ^ 18 = (Q ^ 3) ^ 6 := by ring
      _ ≤ p ^ 6 := Nat.pow_le_pow_left h3 6
  have hp21 : Q ^ 3 ≤ p ^ 2 - 1 := le_trans h3 (by
    have := pow_le_pow_sub_one hp2 (show 1 < 2 by norm_num)
    rwa [pow_one] at this)
  have hp31 : Q ^ 6 ≤ p ^ 3 - 1 := by
    have h1 := pow_le_pow_sub_one hp2 (show 2 < 3 by norm_num)
    have h2 : Q ^ 6 ≤ p ^ 2 := by
      calc Q ^ 6 = (Q ^ 3) ^ 2 := by ring
        _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
    omega
  have hp41 : Q ^ 9 ≤ p ^ 4 - 1 := by
    have h1 := pow_le_pow_sub_one hp2 (show 3 < 4 by norm_num)
    have h2 : Q ^ 9 ≤ p ^ 3 := by
      calc Q ^ 9 = (Q ^ 3) ^ 3 := by ring
        _ ≤ p ^ 3 := Nat.pow_le_pow_left h3 3
    omega
  have h8 : 4 ≤ Q ^ 8 := le_trans (by omega : 4 ≤ 2 ^ 8)
    (Nat.pow_le_pow_left hQ2 8)
  calc 4 * ordTrialityD4 Q < 4 * Q ^ 28 :=
        Nat.mul_lt_mul_of_pos_left (ordTrialityD4_lt_pow hQ2) (by norm_num)
    _ ≤ Q ^ 8 * Q ^ 28 := Nat.mul_le_mul_right _ h8
    _ = Q ^ 18 * (Q ^ 3 * Q ^ 6 * Q ^ 9) := by ring
    _ ≤ p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1)) :=
        Nat.mul_le_mul hp6 (Nat.mul_le_mul (Nat.mul_le_mul hp21 hp31) hp41)

theorem lt_psl2_g2 {q x : ℕ} (hq : 3 ≤ q) (hx : q ^ 6 ≤ x + 1) :
    2 * ordG2 q < x * (x ^ 2 - 1) := by
  have hq2 : 2 ≤ q := by omega
  have h5 : q ^ 5 ≤ x := by
    have := pow_le_pow_sub_one hq2 (show 5 < 6 by norm_num)
    omega
  have h10 : q ^ 10 - 1 ≤ x ^ 2 - 1 := by
    have h2 : q ^ 10 ≤ x ^ 2 := by
      calc q ^ 10 = (q ^ 5) ^ 2 := by ring
        _ ≤ x ^ 2 := Nat.pow_le_pow_left h5 2
    omega
  have h15 : 3 * q ^ 14 ≤ q ^ 15 := by
    rw [pow_succ q 14, mul_comm]
    exact Nat.mul_le_mul_left _ hq
  have h514 : q ^ 5 ≤ q ^ 14 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e : q ^ 5 * (q ^ 10 - 1) = q ^ 15 - q ^ 5 := by
    rw [Nat.mul_sub_one, ← pow_add]
  calc 2 * ordG2 q < 2 * q ^ 14 := Nat.mul_lt_mul_of_pos_left (ordG2_lt_pow hq2) (by norm_num)
    _ ≤ q ^ 5 * (q ^ 10 - 1) := by rw [e]; omega
    _ ≤ x * (x ^ 2 - 1) := Nat.mul_le_mul h5 h10

theorem lt_psl2_l3 {x y : ℕ} (hx : 4 ≤ x) (hy : 2 ≤ y) (hyx : y ^ 3 ≤ x + 1) :
    2 * (y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 + 1))) < 3 * (x * (x ^ 2 - 1)) := by
  have h2y : 2 * (y ^ 2 - 1) ≤ y ^ 3 := by
    have : 2 * y ^ 2 ≤ y ^ 3 := by
      rw [pow_succ y 2, mul_comm]
      exact Nat.mul_le_mul_left _ hy
    omega
  have h1 : 2 * (y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 + 1))) ≤ y ^ 3 * (y ^ 3 * (y ^ 3 + 1)) := by
    calc 2 * (y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 + 1)))
        = y ^ 3 * ((2 * (y ^ 2 - 1)) * (y ^ 3 + 1)) := by ring
      _ ≤ y ^ 3 * (y ^ 3 * (y ^ 3 + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2y)
  have h2 : y ^ 3 * (y ^ 3 * (y ^ 3 + 1)) ≤ (x + 1) * ((x + 1) * (x + 2)) :=
    Nat.mul_le_mul hyx (Nat.mul_le_mul hyx (by omega))
  have h3 : (x + 1) * ((x + 1) * (x + 2)) < 3 * (x * (x ^ 2 - 1)) := by
    have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hx2]
    have hx' : (4 : ℤ) ≤ x := by exact_mod_cast hx
    nlinarith
  omega

theorem lt_sl3_g2 {q x : ℕ} (hq : 2 ≤ q) (hx : q ^ 2 ≤ x) :
    ordG2 q < x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := by
  have h3 : q ^ 6 ≤ x ^ 3 := by
    calc q ^ 6 = (q ^ 2) ^ 3 := by ring
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h21 : q ^ 3 ≤ x ^ 2 - 1 := by
    have : q ^ 4 ≤ x ^ 2 := by
      calc q ^ 4 = (q ^ 2) ^ 2 := by ring
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
    have := pow_le_pow_sub_one hq (show 3 < 4 by norm_num)
    omega
  have h31 : q ^ 5 ≤ x ^ 3 - 1 := by
    have := pow_le_pow_sub_one hq (show 5 < 6 by norm_num)
    omega
  calc ordG2 q < q ^ 14 := ordG2_lt_pow hq
    _ = q ^ 6 * (q ^ 3 * q ^ 5) := by ring
    _ ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h21 h31)

theorem lt_sl3_d4 {q x : ℕ} (hq : 2 ≤ q) (hx : q ^ 4 ≤ x) :
    ordTrialityD4 q < x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := by
  have h3 : q ^ 12 ≤ x ^ 3 := by
    calc q ^ 12 = (q ^ 4) ^ 3 := by ring
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h21 : q ^ 7 ≤ x ^ 2 - 1 := by
    have : q ^ 8 ≤ x ^ 2 := by
      calc q ^ 8 = (q ^ 4) ^ 2 := by ring
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
    have := pow_le_pow_sub_one hq (show 7 < 8 by norm_num)
    omega
  have h31 : q ^ 11 ≤ x ^ 3 - 1 := by
    have := pow_le_pow_sub_one hq (show 11 < 12 by norm_num)
    omega
  calc ordTrialityD4 q < q ^ 28 := ordTrialityD4_lt_pow hq
    _ ≤ q ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ = q ^ 12 * (q ^ 7 * q ^ 11) := by ring
    _ ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h21 h31)

theorem lt_l3_l3 {n y : ℕ} (hn : 1 ≤ n) (hy : 2 ^ (4 * n) ≤ y + 1) :
    3 * ((2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1))) <
      y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1)) := by
  set X := 2 ^ (3 * n) with hX
  set Z := 2 ^ (4 * n) with hZ
  have hXZ : X ^ 8 = Z ^ 6 := by
    rw [hX, hZ, ← pow_mul, ← pow_mul]
    ring_nf
  have hZ16 : 16 ≤ Z := by
    rw [hZ]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hy15 : 15 ≤ y := by omega
  have h1 : 3 * (X ^ 3 * ((X ^ 2 - 1) * (X ^ 3 + 1))) ≤ 6 * Z ^ 6 := by
    have ha : X ^ 2 - 1 ≤ X ^ 2 := Nat.sub_le _ _
    have hb : X ^ 3 + 1 ≤ 2 * X ^ 3 := by
      have : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    calc 3 * (X ^ 3 * ((X ^ 2 - 1) * (X ^ 3 + 1))) ≤ 3 * (X ^ 3 * (X ^ 2 * (2 * X ^ 3))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul ha hb))
      _ = 6 * X ^ 8 := by ring
      _ = 6 * Z ^ 6 := by rw [hXZ]
  have h2 : (15 * Z) ^ 6 ≤ (16 * y) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h3 : 14 * y ^ 6 ≤ y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1)) := by
    have ha : 14 * y ≤ y ^ 2 - 1 := by
      have : 15 * y ≤ y ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul_right _ hy15
      omega
    have hb : y ^ 2 ≤ y ^ 3 - 1 := pow_le_pow_sub_one (by omega) (show 2 < 3 by norm_num)
    calc 14 * y ^ 6 = y ^ 3 * ((14 * y) * y ^ 2) := by ring
      _ ≤ y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul ha hb)
  refine Nat.lt_of_mul_lt_mul_left (a := 15 ^ 6) ?_
  calc 15 ^ 6 * (3 * (X ^ 3 * ((X ^ 2 - 1) * (X ^ 3 + 1)))) ≤ 15 ^ 6 * (6 * Z ^ 6) :=
        Nat.mul_le_mul_left _ h1
    _ = 6 * (15 * Z) ^ 6 := by ring
    _ ≤ 6 * (16 * y) ^ 6 := Nat.mul_le_mul_left _ h2
    _ = 100663296 * y ^ 6 := by ring
    _ < 159468750 * y ^ 6 := Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = 15 ^ 6 * (14 * y ^ 6) := by ring
    _ ≤ 15 ^ 6 * (y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1))) := Nat.mul_le_mul_left _ h3

theorem l3_lt_l3 {x : ℕ} (hx : 2 ≤ x) :
    x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) < 3 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1))) ∧
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) < 3 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) := by
  have h8 : 8 ≤ x ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have hpos : 0 < x ^ 3 * (x ^ 2 - 1) := by
    have : 4 ≤ x ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
    exact Nat.mul_pos (by positivity) (by omega)
  constructor
  · calc x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) = x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) := by ring
      _ < x ^ 3 * (x ^ 2 - 1) * (3 * (x ^ 3 - 1)) :=
          Nat.mul_lt_mul_of_pos_left (by omega) hpos
      _ = 3 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1))) := by ring
  · calc x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) = x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) := by ring
      _ < x ^ 3 * (x ^ 2 - 1) * (3 * (x ^ 3 + 1)) :=
          Nat.mul_lt_mul_of_pos_left (by omega) hpos
      _ = 3 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) := by ring

theorem false_of_odd_g2 {N m q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hdvd : 2 ^ N ∣ m)
    (hlt : m < 2 ^ (3 * N)) (h : m = ordG2 q) : False := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e : ordG2 q = (q ^ 2 - 1) ^ 2 * (q ^ 6 * (q ^ 4 + q ^ 2 + 1)) := by
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    unfold ordG2
    zify [hq2, h6]
    ring
  have hodd : Odd (q ^ 6 * (q ^ 4 + q ^ 2 + 1)) :=
    hq.pow.mul ((hq.pow.add_odd hq.pow).add_one)
  have hdvd' : 2 ^ N ∣ (q ^ 2 - 1) ^ 2 := by
    rw [h, e] at hdvd
    exact (Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_right hdvd
  have hpos : 0 < (q ^ 2 - 1) ^ 2 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    exact pow_pos (by omega) 2
  have hle : 2 ^ N ≤ (q ^ 2 - 1) ^ 2 := Nat.le_of_dvd hpos hdvd'
  have hlt4 : (q ^ 2 - 1) ^ 2 < q ^ 4 := by
    calc (q ^ 2 - 1) ^ 2 < (q ^ 2) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
      _ = q ^ 4 := by ring
  have h12 : 2 ^ (3 * N) < q ^ 12 := by
    calc 2 ^ (3 * N) = (2 ^ N) ^ 3 := by rw [← pow_mul, mul_comm]
      _ < (q ^ 4) ^ 3 := Nat.pow_lt_pow_left (hle.trans_lt hlt4) (by norm_num)
      _ = q ^ 12 := by ring
  have := pow_le_ordG2 (q := q) (by omega)
  omega

end CFSG.RankThree.PartTwo.Sec11.KSListsProof
