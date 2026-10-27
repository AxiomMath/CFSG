module

public import CFSG.Quasithin.Vol2.Ch11SecO7g
public import CFSG.Quasithin.Vol2.Ch11SecO7c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem card_of_central_quot {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hZ : Nat.card (Subgroup.center X) ∣ 3) :
    Nat.card Y = Nat.card X ∨ Nat.card Y * 3 = Nat.card X := by
  have h1 : Nat.card X = Nat.card Y * Nat.card π.ker := by
    rw [π.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have h2 : Nat.card π.ker ∣ 3 := (Subgroup.card_dvd_of_le hker).trans hZ
  rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h <;> rw [h] at h1
  · left
    rw [h1, mul_one]
  · right
    exact h1.symm


theorem not_list701Excl_triality {Y : Type} [Group Y] {k c s : ℕ} (hk : 1 ≤ k)
    (hsdef : s = 2 ^ k) (hc : c = 1 ∨ c = 3) (hY : Nat.card Y * c = ordTrialityD4 s) :
    ¬ List701Excl Y := by
  have hs : 2 ≤ s := by
    rw [hsdef]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨hl1, hl2, hl3, hl4⟩ := triality_odd_lt hs
  obtain ⟨v, hvdef⟩ : ∃ v, v = (s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)) := ⟨_, rfl⟩
  rw [← hvdef] at hl1 hl2 hl3 hl4
  have hord : ordTrialityD4 s = 2 ^ (12 * k) * v := by
    rw [ordTrialityD4, hvdef, hsdef, ← pow_mul, mul_comm k 12]
    ring
  have hvodd : Odd v := by
    rw [hvdef]
    refine Odd.mul ?_ ?_
    · have h1 : Even (s ^ 8 + s ^ 4) := by
        rw [hsdef, ← pow_mul, ← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact h1.add_one
    · rw [hsdef]
      exact (odd_pow k 6 hk (by norm_num)).mul (odd_pow k 2 hk (by norm_num))
  obtain ⟨w, hw, hwv⟩ : ∃ w, Odd w ∧ w * c = v := by
    rcases hc with rfl | rfl
    · exact ⟨v, hvodd, mul_one v⟩
    · have h3 : 3 ∣ v := by
        have : 3 ∣ Nat.card Y * 3 := dvd_mul_left 3 _
        rw [hY, hord] at this
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right _ (by norm_num)) this)
      obtain ⟨w, hw⟩ := h3
      refine ⟨w, ?_, by rw [hw]; ring⟩
      rw [hw] at hvodd
      exact (Nat.odd_mul.mp hvodd).2
  have hYc : Nat.card Y = 2 ^ (12 * k) * w := by
    have hc0 : 0 < c := by rcases hc with rfl | rfl <;> norm_num
    apply Nat.eq_of_mul_eq_mul_right hc0
    rw [hY, hord, ← hwv, mul_assoc]
  have hwle : w ≤ v := by
    rw [← hwv]
    exact Nat.le_mul_of_pos_right _ (by rcases hc with rfl | rfl <;> norm_num)
  have epow : ∀ j, (2 : ℕ) ^ (j * k) = s ^ j := fun j => by rw [hsdef, ← pow_mul, mul_comm]
  refine not_list701Excl_of_profile hYc hw (by omega) ?_ ?_ ?_ ?_
  · rw [show 12 * k = 12 * k from rfl, epow 12]
    omega
  · intro m hm hwm
    obtain rfl : m = 4 * k := by omega
    rw [epow 4, ← pow_mul, ← pow_mul] at hwm
    norm_num at hwm
    omega
  · intro m hm hwm
    obtain rfl : m = 3 * k := by omega
    rw [epow 3, ← pow_mul, ← pow_mul] at hwm
    norm_num at hwm
    omega
  · intro m hm hwm
    obtain rfl : m = 2 * k := by omega
    rw [epow 2, ← pow_mul, ← pow_mul] at hwm
    norm_num at hwm
    omega

theorem not_list701Excl_twistedF4 {Y : Type} [Group Y] {k c s : ℕ} (hk : 1 ≤ k)
    (hsdef : s = 2 ^ k) (hc : c = 1 ∨ c = 3) (hY : Nat.card Y * c = ordTwistedF4 s) :
    ¬ List701Excl Y := by
  have hs : 2 ≤ s := by
    rw [hsdef]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨hl1, hl2, hl3, hl4⟩ := twistedF4_odd_lt hs
  obtain ⟨v, hvdef⟩ : ∃ v, v = (s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1) := ⟨_, rfl⟩
  rw [← hvdef] at hl1 hl2 hl3 hl4
  have hord : ordTwistedF4 s = 2 ^ (12 * k) * v := by
    rw [ordTwistedF4, hvdef, hsdef, ← pow_mul, mul_comm k 12]
    ring
  have hvodd : Odd v := by
    rw [hvdef, hsdef]
    have h6 : Odd ((2 ^ k) ^ 6 + 1) :=
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩).add_one
    have h3 : Odd ((2 ^ k) ^ 3 + 1) :=
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩).add_one
    have h1 : Odd (2 ^ k - 1) := by simpa using odd_pow k 1 hk le_rfl
    exact ((h6.mul (odd_pow k 4 hk (by norm_num))).mul h3).mul h1
  obtain ⟨w, hw, hwv⟩ : ∃ w, Odd w ∧ w * c = v := by
    rcases hc with rfl | rfl
    · exact ⟨v, hvodd, mul_one v⟩
    · have h3 : 3 ∣ v := by
        have : 3 ∣ Nat.card Y * 3 := dvd_mul_left 3 _
        rw [hY, hord] at this
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right _ (by norm_num)) this)
      obtain ⟨w, hw⟩ := h3
      refine ⟨w, ?_, by rw [hw]; ring⟩
      rw [hw] at hvodd
      exact (Nat.odd_mul.mp hvodd).2
  have hYc : Nat.card Y = 2 ^ (12 * k) * w := by
    have hc0 : 0 < c := by rcases hc with rfl | rfl <;> norm_num
    apply Nat.eq_of_mul_eq_mul_right hc0
    rw [hY, hord, ← hwv, mul_assoc]
  have hwle : w ≤ v := by
    rw [← hwv]
    exact Nat.le_mul_of_pos_right _ (by rcases hc with rfl | rfl <;> norm_num)
  have epow : ∀ j, (2 : ℕ) ^ (j * k) = s ^ j := fun j => by rw [hsdef, ← pow_mul, mul_comm]
  refine not_list701Excl_of_profile hYc hw (by omega) ?_ ?_ ?_ ?_
  · rw [show 12 * k = 12 * k from rfl, epow 12]
    omega
  · intro m hm hwm
    obtain rfl : m = 4 * k := by omega
    rw [epow 4, ← pow_mul, ← pow_mul] at hwm
    norm_num at hwm
    omega
  · intro m hm hwm
    obtain rfl : m = 3 * k := by omega
    rw [epow 3, ← pow_mul, ← pow_mul] at hwm
    norm_num at hwm
    omega
  · intro m hm hwm
    obtain rfl : m = 2 * k := by omega
    rw [epow 2, ← pow_mul, ← pow_mul] at hwm
    norm_num at hwm
    omega

theorem not_eight_dvd_psl2 {p N : ℕ} (h8 : p % 8 = 3 ∨ p % 8 = 5) (hN : N * 2 = p * (p ^ 2 - 1)) :
    ¬ 8 ∣ N := by
  rcases h8 with h8 | h8
  · obtain ⟨a, rfl⟩ : ∃ a, p = 8 * a + 3 := ⟨p / 8, by omega⟩
    have hq : (8 * a + 3) ^ 2 - 1 = 8 * (8 * a ^ 2 + 6 * a + 1) := Nat.sub_eq_of_eq_add (by ring)
    rw [hq] at hN
    have hN' : N = 4 * ((8 * a + 3) * (8 * a ^ 2 + 6 * a + 1)) := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
      rw [hN]
      ring
    have hodd : Odd ((8 * a + 3) * (8 * a ^ 2 + 6 * a + 1)) := by
      refine Nat.odd_mul.mpr ⟨⟨4 * a + 1, by ring⟩, ⟨4 * a ^ 2 + 3 * a, by ring⟩⟩
    rw [hN']
    obtain ⟨t, ht⟩ := hodd
    rw [ht]
    omega
  · obtain ⟨a, rfl⟩ : ∃ a, p = 8 * a + 5 := ⟨p / 8, by omega⟩
    have hq : (8 * a + 5) ^ 2 - 1 = 8 * (8 * a ^ 2 + 10 * a + 3) := Nat.sub_eq_of_eq_add (by ring)
    rw [hq] at hN
    have hN' : N = 4 * ((8 * a + 5) * (8 * a ^ 2 + 10 * a + 3)) := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
      rw [hN]
      ring
    have hodd : Odd ((8 * a + 5) * (8 * a ^ 2 + 10 * a + 3)) := by
      refine Nat.odd_mul.mpr ⟨⟨4 * a + 2, by ring⟩, ⟨4 * a ^ 2 + 5 * a + 1, by ring⟩⟩
    rw [hN']
    obtain ⟨t, ht⟩ := hodd
    rw [ht]
    omega

theorem not_list701Excl_psl2 {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (hY : Nat.card Y * 2 = p * (p ^ 2 - 1)) : ¬ List701Excl Y := by
  have hn8 := not_eight_dvd_psl2 h8 hY
  have hge : 11 * (11 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := cube_sub_le (by norm_num) hp11
  have h8f : ∀ j m, 1 ≤ m → 1 ≤ j → ∀ x, (2 ^ m) ^ (3 * j) * x ≠ Nat.card Y := by
    intro j m hm hj x h
    apply hn8
    rw [← h]
    refine Dvd.dvd.mul_right ?_ _
    calc 8 = 2 ^ 3 := rfl
      _ ∣ 2 ^ (m * (3 * j)) := Nat.pow_dvd_pow 2 (by nlinarith)
      _ = (2 ^ m) ^ (3 * j) := pow_mul 2 m (3 * j)
  have hpos : 0 < Nat.card Y := by omega
  refine not_list701Excl_of rfl (fun m h => ?_) (fun m h => ?_) (fun m h => ?_) (fun m h => ?_)
    (fun h => ?_) (by omega) ?_
  · exact psl2_ne_two_pow hp hp11 (by rw [← hY, ← h]; ring)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · exact h8f 1 m hm le_rfl _ h
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · apply hn8
      rw [← h]
      refine Dvd.dvd.mul_right ?_ _
      calc 8 = 2 ^ 3 := rfl
        _ ∣ 2 ^ (m * 4) := Nat.pow_dvd_pow 2 (by omega)
        _ = (2 ^ m) ^ 4 := pow_mul 2 m 4
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · exact h8f 2 m hm (by norm_num) _ h
  · have hpY : p ∣ Nat.card Y := by
      have h1 : p ∣ Nat.card Y * 2 := hY ▸ dvd_mul_right p _
      exact Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)) h1
    have h2 := hpY.trans h
    have h3 : p ∣ 2 ^ 6 * 3 ^ 3 * 7 := by norm_num; exact h2
    rcases hp.dvd_mul.mp h3 with h4 | h4
    · rcases hp.dvd_mul.mp h4 with h5 | h5
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h5)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h5)
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h4
      omega
  · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_⟩
    · omega
    · omega
    all_goals exact hn8 (by rw [h]; norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
