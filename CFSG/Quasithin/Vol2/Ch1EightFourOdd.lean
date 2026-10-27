module

public import CFSG.Quasithin.Vol2.Ch1EightFourNum
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.Ch1Four

theorem four_sub_one_eq' (r : ℕ) (hr : 1 ≤ r) : r ^ 4 - 1 = (r ^ 2 - 1) * (r ^ 2 + 1) := by
  have h4 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ hr
  have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  zify [h4, h2]
  ring

theorem three_dvd_sq_sub_one_of_prime {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) : 3 ∣ r ^ 2 - 1 := by
  have h3 : ¬ 3 ∣ r := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h
    omega
  have hmod : r % 3 = 1 ∨ r % 3 = 2 := by omega
  have hsq : r ^ 2 % 3 = 1 := by
    rcases hmod with h | h <;> simp [Nat.pow_mod, h]
  have : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem r2_false_two {r m n : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hm : 2 * m = r ^ 2 * (r ^ 4 - 1))
    (hn : 2 ≤ n) (hm' : m = 2 ^ n * (4 ^ n - 1)) : False := by
  have hr2 : r ≠ 2 := by omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h1 : r ^ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    have : r ^ 2 ∣ 2 * m := ⟨_, hm⟩
    rw [hm', h4, ← mul_assoc, ← pow_succ'] at this
    exact (Nat.Coprime.pow_left 2 ((Nat.coprime_comm.mp
      (Nat.Coprime.pow_left (n + 1) (Nat.coprime_two_left.mpr hrodd))))).dvd_of_dvd_mul_left this
  have h2 := prime_pow_le_of_dvd_sq_sub_one hr hr2
    (by have := Nat.one_le_two_pow (n := n); have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
        |>.trans' (by norm_num); omega) h1
  obtain ⟨a, rfl⟩ := hrodd
  have hs : (2 * a + 1) ^ 2 + 1 = 2 * (2 * a ^ 2 + 2 * a + 1) := by ring
  have hsodd : Odd (2 * a ^ 2 + 2 * a + 1) := ⟨a ^ 2 + a, by ring⟩
  have h3 : 2 ^ n ∣ (2 * a + 1) ^ 2 - 1 := by
    have : 2 ^ (n + 1) ∣ 2 * m := by
      rw [hm']
      exact ⟨4 ^ n - 1, by ring⟩
    rw [hm, four_sub_one_eq' _ (by omega), hs] at this
    have hc : Nat.Coprime (2 ^ (n + 1)) ((2 * a + 1) ^ 2) :=
      coprime_two_pow_of_odd _ (Odd.pow ⟨a, rfl⟩)
    have h' := hc.dvd_of_dvd_mul_left this
    rw [pow_succ, show ((2 * a + 1) ^ 2 - 1) * (2 * (2 * a ^ 2 + 2 * a + 1)) =
      2 * (((2 * a + 1) ^ 2 - 1) * (2 * a ^ 2 + 2 * a + 1)) by ring, mul_comm (2 ^ n)] at h'
    exact (coprime_two_pow_of_odd _ hsodd).dvd_of_dvd_mul_right
      (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h')
  have h5 := two_pow_le_of_dvd_sq_sub_one ⟨a, rfl⟩ (by omega) h3
  nlinarith

theorem r2_three {r m : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hm : 2 * m = r ^ 2 * (r ^ 4 - 1)) :
    3 ∣ m := by
  have h1 : 3 ∣ 2 * m := by
    rw [hm, four_sub_one_eq' r (by omega)]
    exact Dvd.dvd.mul_left ((three_dvd_sq_sub_one_of_prime hr hr5).mul_right _) _
  exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 3 2) h1

theorem r2_false_p {r m p c k : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hm : 2 * m = r ^ 2 * (r ^ 4 - 1))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hc : c = 1 ∨ c = 3) (h : m * 2 ^ k = c * (p * (p ^ 2 - 1))) :
    False := by
  have hr2 : r ≠ 2 := by omega
  have hp2 : p ≠ 2 := by omega
  have hrodd := hr.odd_of_ne_two hr2
  have hpodd := hp.odd_of_ne_two hp2
  have hpm : p ∣ m :=
    prime_dvd_of_dvd_mul_two_pow hp hp2 (h ▸ dvd_mul_of_dvd_right (dvd_mul_right p _) c)
  have hp1 : 1 ≤ p ^ 2 - 1 := by
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  by_cases hpr : p = r
  · subst hpr
    have e : p * (p ^ 2 - 1) * (p * (p ^ 2 + 1) * 2 ^ k) = p * (p ^ 2 - 1) * (2 * c) := by
      calc p * (p ^ 2 - 1) * (p * (p ^ 2 + 1) * 2 ^ k) = 2 * m * 2 ^ k := by
            rw [hm, four_sub_one_eq' p (by omega)]; ring
        _ = 2 * (m * 2 ^ k) := by ring
        _ = p * (p ^ 2 - 1) * (2 * c) := by rw [h]; ring
    have e' := Nat.eq_of_mul_eq_mul_left (by positivity) e
    have h25 : 25 ≤ p ^ 2 := by nlinarith
    have h130 : 5 * 26 ≤ p * (p ^ 2 + 1) * 2 ^ k :=
      calc 5 * 26 ≤ p * (p ^ 2 + 1) := Nat.mul_le_mul hp5 (by omega)
        _ = p * (p ^ 2 + 1) * 1 := (mul_one _).symm
        _ ≤ p * (p ^ 2 + 1) * 2 ^ k := Nat.mul_le_mul_left _ Nat.one_le_two_pow
    rcases hc with rfl | rfl <;> omega
  ·
    have hr2p : r ^ 2 ∣ p ^ 2 - 1 := by
      have h1 : r ^ 2 ∣ 2 * m * 2 ^ k := Dvd.dvd.mul_right ⟨_, hm⟩ _
      rw [mul_assoc, h, show 2 * (c * (p * (p ^ 2 - 1))) = (2 * c * p) * (p ^ 2 - 1) by ring]
        at h1
      have hc' : Nat.Coprime (r ^ 2) (2 * c * p) := by
        refine Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_)
        · exact (Nat.coprime_primes hr Nat.prime_two).mpr hr2
        · rcases hc with rfl | rfl
          · exact Nat.coprime_one_right _
          · exact (Nat.coprime_primes hr Nat.prime_three).mpr (by omega)
        · exact (Nat.coprime_primes hr hp).mpr (Ne.symm hpr)
      exact hc'.dvd_of_dvd_mul_left h1
    have h2 := prime_pow_le_of_dvd_sq_sub_one hr hr2 (by omega) hr2p
    have h3 : p ∣ (r + 1) * (r - 1) * (r ^ 2 + 1) := by
      have : p ∣ 2 * m := hpm.mul_left 2
      rw [hm] at this
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)) hpr
      · rwa [four_sub_one_eq' r (by omega), sq_sub_one_eq] at h
    have h4 : p ≤ r ^ 2 + 1 := by
      have hr1 : r ≤ r ^ 2 := by nlinarith
      rcases (Nat.Prime.dvd_mul hp).mp h3 with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · have := Nat.le_of_dvd (by omega) h'
          omega
        · have := Nat.le_of_dvd (by omega) h'
          omega
      · exact Nat.le_of_dvd (by positivity) h
    have h5 : p ≠ r ^ 2 := fun he => hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp
      (he ▸ dvd_pow_self r two_ne_zero)).symm
    have h6 : (r ^ 2) % 2 = 1 := Nat.odd_iff.mp (hrodd.pow)
    have h7 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    omega

theorem prime_dvd_yl {r : ℕ} (hr : r.Prime) (h : r ∣ 244823040) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 23 := by
  have e : (244823040 : ℕ) = [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 7, 11, 23].prod := by
    norm_num
  rw [e] at h
  have := mem_of_prime_dvd_prod hr _ (by decide) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  omega

theorem r2_false_fix {r m k : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hm : 2 * m = r ^ 2 * (r ^ 4 - 1))
    (h : m * 2 ^ k ∣ 244823040) : False := by
  have hr2 : r ≠ 2 := by omega
  have hmY : m ∣ 244823040 := (dvd_mul_right m _).trans h
  have hrm : r ∣ m := by
    have : r ∣ 2 * m := ⟨r * (r ^ 4 - 1), by rw [hm]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hr Nat.prime_two).mpr hr2) this)
  have h2 : r ^ 2 ∣ 2 * 244823040 := (Dvd.intro _ hm.symm).trans (Nat.mul_dvd_mul_left 2 hmY)
  rcases prime_dvd_yl hr (hrm.trans hmY) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

@[expose] def OddL3Shape (m : ℕ) : Prop :=
  ∃ p d E : ℕ, p.Prime ∧ 3 ≤ p ∧ m * d = p ^ 3 * ((p ^ 2 - 1) * E) ∧
    ((E = p ^ 3 - 1 ∧ (d = 1 ∨ (d = 3 ∧ 3 ∣ p - 1))) ∨
      (E = p ^ 3 + 1 ∧ (d = 1 ∨ (d = 3 ∧ 3 ∣ p + 1))))

theorem OddL3Shape.facts {m : ℕ} (h : OddL3Shape m) :
    ∃ p d E : ℕ, p.Prime ∧ 3 ≤ p ∧ (d = 1 ∨ d = 3) ∧ (p = 3 → d = 1) ∧
      m * d = p ^ 3 * ((p ^ 2 - 1) * E) ∧ p ^ 3 - 1 ≤ E ∧ E ≤ p ^ 3 + 1 ∧ p ^ 3 ∣ m ∧ 3 ∣ m ∧
      (∀ q, q.Prime → q ≠ p → q ∣ m → q ≤ p ^ 2 + p + 1) ∧ 0 < m := by
  obtain ⟨p, d, E, hp, hp3, hm, hE⟩ := h
  have hp1 : 1 ≤ p := by omega
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hp2 : p ≠ 2 := by omega
  have hd : d = 1 ∨ d = 3 := by rcases hE with ⟨-, h | ⟨h, -⟩⟩ | ⟨-, h | ⟨h, -⟩⟩ <;> simp [h]
  have hd3 : p = 3 → d = 1 := by
    rintro rfl
    rcases hE with ⟨-, h | ⟨-, h⟩⟩ | ⟨-, h | ⟨-, h⟩⟩ <;> first | exact h | omega
  have hE1 : p ^ 3 - 1 ≤ E ∧ E ≤ p ^ 3 + 1 := by
    rcases hE with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  have hEpos : 0 < E := by
    have : 27 ≤ p ^ 3 := by nlinarith
    omega
  have hsq : 0 < p ^ 2 - 1 := by
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hmpos : 0 < m := by
    by_contra h0
    push Not at h0
    have : m = 0 := by omega
    rw [this, zero_mul] at hm
    have : 0 < p ^ 3 * ((p ^ 2 - 1) * E) := by positivity
    omega
  have hp3m : p ^ 3 ∣ m := by
    have h1 : p ^ 3 ∣ m * d := ⟨_, hm⟩
    rcases hd with rfl | rfl
    · simpa using h1
    · have hp3' : p ≠ 3 := fun h => by have := hd3 h; omega
      exact (Nat.Coprime.pow_left 3
        ((Nat.coprime_primes hp Nat.prime_three).mpr hp3')).dvd_of_dvd_mul_right h1
  refine ⟨p, d, E, hp, hp3, hd, hd3, hm, hE1.1, hE1.2, hp3m, ?_, ?_, hmpos⟩
  ·
    by_cases h3 : p = 3
    · subst h3
      exact (dvd_pow_self 3 (by norm_num)).trans hp3m
    · have h31 : 3 ∣ p ^ 2 - 1 := by
        have h' : ¬ 3 ∣ p := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
        have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
        have hsq : p ^ 2 % 3 = 1 := by rcases hmod with h | h <;> simp [Nat.pow_mod, h]
        have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      rcases hd with rfl | rfl
      · rw [mul_one] at hm
        rw [hm]
        exact Dvd.dvd.mul_left (h31.mul_right _) _
      ·
        have h9 : 3 * 3 ∣ (p ^ 2 - 1) * E := by
          rcases hE with ⟨rfl, h0 | ⟨-, h⟩⟩ | ⟨rfl, h0 | ⟨-, h⟩⟩
          · omega
          · refine Nat.mul_dvd_mul h31 ?_
            have e : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
              have : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
              zify [hp1, this]
              ring
            rw [e]
            exact h.mul_right _
          · omega
          · refine Nat.mul_dvd_mul h31 ?_
            have e : p ^ 3 + 1 = (p + 1) * (p ^ 2 - p + 1) := by
              zify [hpp]
              ring
            rw [e]
            exact h.mul_right _
        have : 3 * 3 ∣ m * 3 := hm ▸ h9.mul_left _
        rw [mul_comm m 3] at this
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  · intro q hq hqp hqm
    have h1 : q ∣ p ^ 3 * ((p ^ 2 - 1) * E) := hm ▸ hqm.mul_right d
    have h2 : q ∣ (p ^ 2 - 1) * E := by
      rcases (Nat.Prime.dvd_mul hq).mp h1 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)) hqp
      · exact h
    rcases (Nat.Prime.dvd_mul hq).mp h2 with h | h
    · rw [sq_sub_one_eq] at h
      rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · have := Nat.le_of_dvd (by omega) h'
        omega
    · rcases hE with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · have e : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
          have : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
          zify [hp1, this]
          ring
        rw [e] at h
        rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
        · have := Nat.le_of_dvd (by omega) h'
          omega
        · exact Nat.le_of_dvd (by positivity) h'
      · have e : p ^ 3 + 1 = (p + 1) * (p ^ 2 - p + 1) := by
          zify [hpp]
          ring
        rw [e] at h
        rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
        · have := Nat.le_of_dvd (by omega) h'
          omega
        · have := Nat.le_of_dvd (by omega) h'
          omega

theorem dvd_of_mul_two_pow_eq {m0 y0 k : ℕ} (h : m0 * 2 ^ k = y0) : m0 ∣ y0 := ⟨_, h.symm⟩

theorem false_of_mul_two_pow_eq {m0 y0 k q : ℕ} (h : m0 * 2 ^ k = y0) (hm0 : 0 < m0)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqm : q * m0 ∣ y0) : False := by
  rw [← h, mul_comm q] at hqm
  exact prime_not_dvd_two_pow hq hq2 k (Nat.dvd_of_mul_dvd_mul_left hm0 hqm)

theorem OddL3Shape.false_of_two {m n : ℕ} (h : OddL3Shape m) (hn : 2 ≤ n)
    (hm : m = 2 ^ n * (4 ^ n - 1)) : False := by
  obtain ⟨p, d, E, hp, hp3, hd, -, hmd, -, hE, hp3m, -, -, -⟩ := h.facts
  have hp2 : p ≠ 2 := by omega
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : p ^ 3 ∣ (2 ^ n) ^ 2 - 1 := by
    rw [hm, h4] at hp3m
    exact (Nat.Coprime.pow_left 3 ((Nat.coprime_comm.mp (Nat.Coprime.pow_left n
      (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)))))).dvd_of_dvd_mul_left hp3m
  have h2 := prime_pow_le_of_dvd_sq_sub_one hp hp2 (by omega) h1
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hup : m ≤ p ^ 3 * (p ^ 2 * (p ^ 3 + 1)) := by
    calc m ≤ m * d := Nat.le_mul_of_pos_right _ hd1
      _ = p ^ 3 * ((p ^ 2 - 1) * E) := hmd
      _ ≤ p ^ 3 * (p ^ 2 * (p ^ 3 + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) hE)
  set X := 2 ^ n with hX
  have hX' : p ^ 3 - 1 ≤ X := by omega
  have hlow : (p ^ 3 - 1) * ((p ^ 3 - 1) ^ 2 - 1) ≤ m := by
    rw [hm, h4]
    exact Nat.mul_le_mul hX' (Nat.sub_le_sub_right (Nat.pow_le_pow_left hX' 2) 1)
  have hp27 : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  set Y := p ^ 3 with hY
  have hkey : (Y - 1) * ((Y - 1) ^ 2 - 1) = Y * ((Y - 1) * (Y - 2)) := by
    have : 1 ≤ (Y - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ Y), (by omega : 2 ≤ Y)]
    ring
  rw [hkey] at hlow
  have hcmp : p ^ 2 * (Y + 1) < (Y - 1) * (Y - 2) := by
    have hY6 : Y * Y = p ^ 6 := by rw [hY]; ring
    have hp5 : p ^ 5 * 3 ≤ p ^ 6 := by
      rw [show p ^ 6 = p ^ 5 * p by ring]
      exact Nat.mul_le_mul_left _ hp3
    have hp53 : p ^ 3 * 9 ≤ p ^ 5 := by
      rw [show p ^ 5 = p ^ 3 * p ^ 2 by ring]
      exact Nat.mul_le_mul_left _ (by nlinarith)
    have hp2Y : p ^ 2 * Y = p ^ 5 := by rw [hY]; ring
    have hp23 : p ^ 2 ≤ Y := by rw [hY]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
    zify [(by omega : 1 ≤ Y), (by omega : 2 ≤ Y)]
    nlinarith
  have : Y * (p ^ 2 * (Y + 1)) < Y * ((Y - 1) * (Y - 2)) :=
    Nat.mul_lt_mul_of_pos_left hcmp (by omega)
  have e : p ^ 3 * (p ^ 2 * (p ^ 3 + 1)) = Y * (p ^ 2 * (Y + 1)) := by rw [hY]
  omega

theorem OddL3Shape.three {m : ℕ} (h : OddL3Shape m) : 3 ∣ m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3, -, -⟩ := h.facts
  exact h3

theorem OddL3Shape.false_of_p {m l c k : ℕ} (h : OddL3Shape m) (hl : l.Prime) (hl5 : 5 ≤ l)
    (hc : c = 1 ∨ c = 3) (hm : m * 2 ^ k = c * (l * (l ^ 2 - 1))) : False := by
  obtain ⟨p, d, E, hp, hp3, hd, -, hmd, -, -, hp3m, -, hq, -⟩ := h.facts
  have hp2 : p ≠ 2 := by omega
  have hl2 : l ≠ 2 := by omega
  have hlm : l ∣ m :=
    prime_dvd_of_dvd_mul_two_pow hl hl2 (hm ▸ dvd_mul_of_dvd_right (dvd_mul_right l _) c)
  have h1 : p ^ 3 ∣ c * (l * (l ^ 2 - 1)) := hm ▸ hp3m.mul_right _
  by_cases hlp : l = p
  · subst hlp
    have h2 : l ^ 2 ∣ c * (l ^ 2 - 1) := by
      rw [show c * (l * (l ^ 2 - 1)) = l * (c * (l ^ 2 - 1)) by ring,
        show l ^ 3 = l * l ^ 2 by ring] at h1
      exact Nat.dvd_of_mul_dvd_mul_left hl.pos h1
    have h3 : l ∣ c * (l ^ 2 - 1) := (dvd_pow_self l two_ne_zero).trans h2
    rcases (Nat.Prime.dvd_mul hl).mp h3 with h4 | h4
    · have := Nat.le_of_dvd (by rcases hc with rfl | rfl <;> norm_num) h4
      rcases hc with rfl | rfl <;> omega
    · have h5 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
      have h6 : l ∣ l ^ 2 - (l ^ 2 - 1) := Nat.dvd_sub h5 h4
      rw [show l ^ 2 - (l ^ 2 - 1) = 1 by have := Nat.one_le_pow 2 l hl.pos; omega] at h6
      exact hl.one_lt.ne' (Nat.dvd_one.mp h6)
  · have hlq := hq l hl hlp hlm
    by_cases hp3' : p = 3
    · subst hp3'
      have h9 : 3 ^ 2 ∣ l ^ 2 - 1 := by
        have hc27 : 3 ^ 3 ∣ c * (l ^ 2 - 1) := by
          rw [show c * (l * (l ^ 2 - 1)) = l * (c * (l ^ 2 - 1)) by ring] at h1
          exact (Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_three hl).mpr
            (Ne.symm hlp))).dvd_of_dvd_mul_left h1
        rcases hc with rfl | rfl
        · rw [one_mul] at hc27
          exact (pow_dvd_pow 3 (by norm_num)).trans hc27
        · rw [show 3 ^ 3 = 3 * 3 ^ 2 by norm_num] at hc27
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hc27
      have h10 := prime_pow_le_of_dvd_sq_sub_one Nat.prime_three (by norm_num) (by omega) h9
      norm_num at hlq h10
      rcases prime_pow_dvd_of_dvd_sq_sub_one Nat.prime_three (by norm_num) (by omega) h9 with
        h11 | h11 <;> interval_cases l <;> first | omega | exact absurd hl (by norm_num)
    ·
      have h2 : p ^ 3 ∣ l ^ 2 - 1 := by
        rw [show c * (l * (l ^ 2 - 1)) = (c * l) * (l ^ 2 - 1) by ring] at h1
        have hcop : Nat.Coprime (p ^ 3) (c * l) := by
          refine Nat.Coprime.pow_left 3 (Nat.Coprime.mul_right ?_ ?_)
          · rcases hc with rfl | rfl
            · exact Nat.coprime_one_right _
            · exact (Nat.coprime_primes hp Nat.prime_three).mpr hp3'
          · exact (Nat.coprime_primes hp hl).mpr (Ne.symm hlp)
        exact hcop.dvd_of_dvd_mul_left h1
      have h3 := prime_pow_le_of_dvd_sq_sub_one hp hp2 (by omega) h2
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p <;> omega
        · exact h
      have : p ^ 3 = p * p ^ 2 := by ring
      nlinarith

theorem OddL3Shape.small_of_fix {m k y : ℕ} (h : OddL3Shape m) (hy : y ∣ 244823040)
    (hm : m * 2 ^ k = y) : m = 5616 ∨ m = 5832 ∨ m = 6048 := by
  obtain ⟨p, d, E, hp, hp3, hd, hd3, hmd, hE1, hE2, hp3m, -, -, -⟩ := h.facts
  have h1 : p ^ 3 ∣ 244823040 := (hp3m.trans (dvd_of_mul_two_pow_eq hm)).trans hy
  have h2 : p ∣ 244823040 := (dvd_pow_self p (by norm_num)).trans h1
  rcases prime_dvd_yl hp h2 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · have := hd3 rfl
    subst this
    norm_num at hmd hE1 hE2
    interval_cases E <;> omega
  all_goals exact absurd h1 (by norm_num)

end CFSG.Quasithin.Ch1Four
