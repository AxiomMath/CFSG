module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.KGC31

theorem kgC31Ord_two_pow_mod_eleven (f : ℕ) : 2 ^ f % 11 = 2 ^ (f % 10) % 11 := by
  have h10 : 2 ^ 10 ≡ 1 [MOD 11] := by decide
  have hpow : (2 ^ 10) ^ (f / 10) ≡ 1 [MOD 11] := by simpa using h10.pow (f / 10)
  have hf : 2 ^ f = (2 ^ 10) ^ (f / 10) * 2 ^ (f % 10) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h := hpow.mul_right (2 ^ (f % 10))
  rw [one_mul] at h
  rw [hf]
  exact h

theorem kgC31Ord_two_pow_mod_five (f : ℕ) : 2 ^ f % 5 = 2 ^ (f % 4) % 5 := by
  have h4 : 2 ^ 4 ≡ 1 [MOD 5] := by decide
  have hpow : (2 ^ 4) ^ (f / 4) ≡ 1 [MOD 5] := by simpa using h4.pow (f / 4)
  have hf : 2 ^ f = (2 ^ 4) ^ (f / 4) * 2 ^ (f % 4) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h := hpow.mul_right (2 ^ (f % 4))
  rw [one_mul] at h
  rw [hf]
  exact h

theorem kgC31Ord_two_pow_mod_seven (f : ℕ) : 2 ^ f % 7 = 2 ^ (f % 3) % 7 := by
  have h3 : 2 ^ 3 ≡ 1 [MOD 7] := by decide
  have hpow : (2 ^ 3) ^ (f / 3) ≡ 1 [MOD 7] := by simpa using h3.pow (f / 3)
  have hf : 2 ^ f = (2 ^ 3) ^ (f / 3) * 2 ^ (f % 3) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h := hpow.mul_right (2 ^ (f % 3))
  rw [one_mul] at h
  rw [hf]
  exact h

theorem kgC31Ord_not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (n : ℕ) :
    ¬ p ∣ 2 ^ n :=
  fun h => hp2 (hp.dvd_of_dvd_pow h)

theorem kgC31Ord_not_dvd_pow_two_pow {p : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (f k : ℕ) :
    ¬ p ∣ (2 ^ f) ^ k := by
  rw [← pow_mul]
  exact kgC31Ord_not_dvd_two_pow hp hp2 (f * k)

theorem kgC31Ord_five_dvd_of_eleven_dvd_pow_six (f : ℕ) (h : 11 ∣ (2 ^ f) ^ 6 - 1) :
    5 ∣ f := by
  have hpos : 0 < (2 ^ f) ^ 6 := by positivity
  have h1 : (2 ^ f) ^ 6 % 11 = 1 := by omega
  have h2 : (2 ^ f) ^ 6 % 11 = (2 ^ f % 11) ^ 6 % 11 := Nat.pow_mod _ _ _
  rw [kgC31Ord_two_pow_mod_eleven f] at h2
  have key : ∀ r, r < 10 → (2 ^ r % 11) ^ 6 % 11 = 1 → r % 5 = 0 := by decide
  have hr := key (f % 10) (Nat.mod_lt _ (by norm_num)) (by rw [← h2, h1])
  omega

theorem kgC31Ord_five_dvd_of_eleven_dvd_pow_two (f : ℕ) (h : 11 ∣ (2 ^ f) ^ 2 - 1) :
    5 ∣ f := by
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  have h1 : (2 ^ f) ^ 2 % 11 = 1 := by omega
  have h2 : (2 ^ f) ^ 2 % 11 = (2 ^ f % 11) ^ 2 % 11 := Nat.pow_mod _ _ _
  rw [kgC31Ord_two_pow_mod_eleven f] at h2
  have key : ∀ r, r < 10 → (2 ^ r % 11) ^ 2 % 11 = 1 → r % 5 = 0 := by decide
  have hr := key (f % 10) (Nat.mod_lt _ (by norm_num)) (by rw [← h2, h1])
  omega

theorem kgC31Ord_five_dvd_of_eleven_dvd_pow_four_sub_one (f : ℕ) (h : 11 ∣ (2 ^ f) ^ 4 - 1) :
    5 ∣ f := by
  have hpos : 0 < (2 ^ f) ^ 4 := by positivity
  have h1 : (2 ^ f) ^ 4 % 11 = 1 := by omega
  have h2 : (2 ^ f) ^ 4 % 11 = (2 ^ f % 11) ^ 4 % 11 := Nat.pow_mod _ _ _
  rw [kgC31Ord_two_pow_mod_eleven f] at h2
  have key : ∀ r, r < 10 → (2 ^ r % 11) ^ 4 % 11 = 1 → r % 5 = 0 := by decide
  have hr := key (f % 10) (Nat.mod_lt _ (by norm_num)) (by rw [← h2, h1])
  omega

theorem kgC31Ord_five_dvd_of_eleven_dvd_pow_three_add_one (f : ℕ)
    (h : 11 ∣ (2 ^ f) ^ 3 + 1) : 5 ∣ f := by
  have e : (2 ^ f % 11) ^ 3 + 1 ≡ (2 ^ f) ^ 3 + 1 [MOD 11] :=
    ((Nat.mod_modEq _ _).pow 3).add_right 1
  have e' : ((2 ^ f % 11) ^ 3 + 1) % 11 = ((2 ^ f) ^ 3 + 1) % 11 := e
  rw [Nat.mod_eq_zero_of_dvd h, kgC31Ord_two_pow_mod_eleven f] at e'
  have key : ∀ r, r < 10 → ((2 ^ r % 11) ^ 3 + 1) % 11 = 0 → r % 5 = 0 := by decide
  have hr := key (f % 10) (Nat.mod_lt _ (by norm_num)) e'
  omega

theorem kgC31Ord_five_dvd_of_eleven_dvd_two_pow_sub_one (f : ℕ) (h : 11 ∣ 2 ^ f - 1) :
    5 ∣ f := by
  have hpos : 0 < 2 ^ f := by positivity
  have h1 : 2 ^ f % 11 = 1 := by omega
  rw [kgC31Ord_two_pow_mod_eleven f] at h1
  have key : ∀ r, r < 10 → 2 ^ r % 11 = 1 → r % 5 = 0 := by decide
  have hr := key (f % 10) (Nat.mod_lt _ (by norm_num)) h1
  omega

theorem kgC31Ord_two_dvd_of_five_dvd_pow_six (f : ℕ) (h : 5 ∣ (2 ^ f) ^ 6 - 1) : 2 ∣ f := by
  have hpos : 0 < (2 ^ f) ^ 6 := by positivity
  have h1 : (2 ^ f) ^ 6 % 5 = 1 := by omega
  have h2 : (2 ^ f) ^ 6 % 5 = (2 ^ f % 5) ^ 6 % 5 := Nat.pow_mod _ _ _
  rw [kgC31Ord_two_pow_mod_five f] at h2
  have key : ∀ r, r < 4 → (2 ^ r % 5) ^ 6 % 5 = 1 → r % 2 = 0 := by decide
  have hr := key (f % 4) (Nat.mod_lt _ (by norm_num)) (by rw [← h2, h1])
  omega

theorem kgC31Ord_two_dvd_of_five_dvd_pow_two (f : ℕ) (h : 5 ∣ (2 ^ f) ^ 2 - 1) : 2 ∣ f := by
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  have h1 : (2 ^ f) ^ 2 % 5 = 1 := by omega
  have h2 : (2 ^ f) ^ 2 % 5 = (2 ^ f % 5) ^ 2 % 5 := Nat.pow_mod _ _ _
  rw [kgC31Ord_two_pow_mod_five f] at h2
  have key : ∀ r, r < 4 → (2 ^ r % 5) ^ 2 % 5 = 1 → r % 2 = 0 := by decide
  have hr := key (f % 4) (Nat.mod_lt _ (by norm_num)) (by rw [← h2, h1])
  omega

theorem kgC31Ord_three_dvd_of_seven_dvd_pow_four_sub_one (f : ℕ) (h : 7 ∣ (2 ^ f) ^ 4 - 1) :
    3 ∣ f := by
  have hpos : 0 < (2 ^ f) ^ 4 := by positivity
  have h1 : (2 ^ f) ^ 4 % 7 = 1 := by omega
  have h2 : (2 ^ f) ^ 4 % 7 = (2 ^ f % 7) ^ 4 % 7 := Nat.pow_mod _ _ _
  rw [kgC31Ord_two_pow_mod_seven f] at h2
  have key : ∀ r, r < 3 → (2 ^ r % 7) ^ 4 % 7 = 1 → r % 3 = 0 := by decide
  have hr := key (f % 3) (Nat.mod_lt _ (by norm_num)) (by rw [← h2, h1])
  omega

theorem kgC31Ord_three_dvd_of_seven_dvd_two_pow_sub_one (f : ℕ) (h : 7 ∣ 2 ^ f - 1) :
    3 ∣ f := by
  have hpos : 0 < 2 ^ f := by positivity
  have h1 : 2 ^ f % 7 = 1 := by omega
  rw [kgC31Ord_two_pow_mod_seven f] at h1
  have key : ∀ r, r < 3 → 2 ^ r % 7 = 1 → r % 3 = 0 := by decide
  have hr := key (f % 3) (Nat.mod_lt _ (by norm_num)) h1
  omega

theorem kgC31Ord_not_eleven_dvd_pow_eight_add (f : ℕ) :
    ¬ 11 ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 := by
  intro h
  have e : (2 ^ f % 11) ^ 8 + (2 ^ f % 11) ^ 4 + 1 ≡ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 [MOD 11] :=
    (((Nat.mod_modEq _ _).pow 8).add ((Nat.mod_modEq _ _).pow 4)).add_right 1
  have e' : ((2 ^ f % 11) ^ 8 + (2 ^ f % 11) ^ 4 + 1) % 11
      = ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) % 11 := e
  rw [Nat.mod_eq_zero_of_dvd h, kgC31Ord_two_pow_mod_eleven f] at e'
  have key : ∀ r, r < 10 → ((2 ^ r % 11) ^ 8 + (2 ^ r % 11) ^ 4 + 1) % 11 ≠ 0 := by decide
  exact key (f % 10) (Nat.mod_lt _ (by norm_num)) e'

theorem kgC31Ord_not_five_dvd_pow_eight_add (f : ℕ) :
    ¬ 5 ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 := by
  intro h
  have e : (2 ^ f % 5) ^ 8 + (2 ^ f % 5) ^ 4 + 1 ≡ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 [MOD 5] :=
    (((Nat.mod_modEq _ _).pow 8).add ((Nat.mod_modEq _ _).pow 4)).add_right 1
  have e' : ((2 ^ f % 5) ^ 8 + (2 ^ f % 5) ^ 4 + 1) % 5
      = ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) % 5 := e
  rw [Nat.mod_eq_zero_of_dvd h, kgC31Ord_two_pow_mod_five f] at e'
  have key : ∀ r, r < 4 → ((2 ^ r % 5) ^ 8 + (2 ^ r % 5) ^ 4 + 1) % 5 ≠ 0 := by decide
  exact key (f % 4) (Nat.mod_lt _ (by norm_num)) e'

theorem kgC31Ord_not_seven_dvd_pow_six_add_one (f : ℕ) : ¬ 7 ∣ (2 ^ f) ^ 6 + 1 := by
  intro h
  have e : (2 ^ f % 7) ^ 6 + 1 ≡ (2 ^ f) ^ 6 + 1 [MOD 7] :=
    ((Nat.mod_modEq _ _).pow 6).add_right 1
  have e' : ((2 ^ f % 7) ^ 6 + 1) % 7 = ((2 ^ f) ^ 6 + 1) % 7 := e
  rw [Nat.mod_eq_zero_of_dvd h, kgC31Ord_two_pow_mod_seven f] at e'
  have key : ∀ r, r < 3 → ((2 ^ r % 7) ^ 6 + 1) % 7 ≠ 0 := by decide
  exact key (f % 3) (Nat.mod_lt _ (by norm_num)) e'

theorem kgC31Ord_not_seven_dvd_pow_three_add_one (f : ℕ) : ¬ 7 ∣ (2 ^ f) ^ 3 + 1 := by
  intro h
  have e : (2 ^ f % 7) ^ 3 + 1 ≡ (2 ^ f) ^ 3 + 1 [MOD 7] :=
    ((Nat.mod_modEq _ _).pow 3).add_right 1
  have e' : ((2 ^ f % 7) ^ 3 + 1) % 7 = ((2 ^ f) ^ 3 + 1) % 7 := e
  rw [Nat.mod_eq_zero_of_dvd h, kgC31Ord_two_pow_mod_seven f] at e'
  have key : ∀ r, r < 3 → ((2 ^ r % 7) ^ 3 + 1) % 7 ≠ 0 := by decide
  exact key (f % 3) (Nat.mod_lt _ (by norm_num)) e'

theorem kgC31Ord_not_eleven_dvd_pow_six_add_one (f : ℕ) : ¬ 11 ∣ (2 ^ f) ^ 6 + 1 := by
  intro h
  have e : (2 ^ f % 11) ^ 6 + 1 ≡ (2 ^ f) ^ 6 + 1 [MOD 11] :=
    ((Nat.mod_modEq _ _).pow 6).add_right 1
  have e' : ((2 ^ f % 11) ^ 6 + 1) % 11 = ((2 ^ f) ^ 6 + 1) % 11 := e
  rw [Nat.mod_eq_zero_of_dvd h, kgC31Ord_two_pow_mod_eleven f] at e'
  have key : ∀ r, r < 10 → ((2 ^ r % 11) ^ 6 + 1) % 11 ≠ 0 := by decide
  exact key (f % 10) (Nat.mod_lt _ (by norm_num)) e'

theorem kgC31Ord_ten_dvd_of_G2_order (f : ℕ)
    (h : 443520 ∣ 2 ^ (6 * f) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) : 10 ∣ f := by
  have hp11 : Nat.Prime 11 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have h11 : 11 ∣ 2 ^ (6 * f) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) :=
    dvd_trans (by norm_num) h
  have h5 : 5 ∣ 2 ^ (6 * f) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) :=
    dvd_trans (by norm_num) h
  have h5f : 5 ∣ f := by
    rcases (Nat.Prime.dvd_mul hp11).1 h11 with h1 | h1
    · exact absurd h1 (kgC31Ord_not_dvd_two_pow hp11 (by norm_num) _)
    · rcases (Nat.Prime.dvd_mul hp11).1 h1 with h2 | h2
      · exact kgC31Ord_five_dvd_of_eleven_dvd_pow_six f h2
      · exact kgC31Ord_five_dvd_of_eleven_dvd_pow_two f h2
  have h2f : 2 ∣ f := by
    rcases (Nat.Prime.dvd_mul hp5).1 h5 with h1 | h1
    · exact absurd h1 (kgC31Ord_not_dvd_two_pow hp5 (by norm_num) _)
    · rcases (Nat.Prime.dvd_mul hp5).1 h1 with h2 | h2
      · exact kgC31Ord_two_dvd_of_five_dvd_pow_six f h2
      · exact kgC31Ord_two_dvd_of_five_dvd_pow_two f h2
  omega

theorem kgC31Ord_ten_dvd_of_D4_order (f : ℕ)
    (h : 443520 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1)
      * ((2 ^ f) ^ 2 - 1)) :
    10 ∣ f := by
  have hp11 : Nat.Prime 11 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have h11 : 11 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1)
      * ((2 ^ f) ^ 2 - 1) := dvd_trans (by norm_num) h
  have h5 : 5 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1)
      * ((2 ^ f) ^ 2 - 1) := dvd_trans (by norm_num) h
  have h5f : 5 ∣ f := by
    simp only [Nat.Prime.dvd_mul hp11, or_assoc] at h11
    rcases h11 with h1 | h1 | h1 | h1
    · exact absurd h1 (kgC31Ord_not_dvd_pow_two_pow hp11 (by norm_num) f 12)
    · exact absurd h1 (kgC31Ord_not_eleven_dvd_pow_eight_add f)
    · exact kgC31Ord_five_dvd_of_eleven_dvd_pow_six f h1
    · exact kgC31Ord_five_dvd_of_eleven_dvd_pow_two f h1
  have h2f : 2 ∣ f := by
    simp only [Nat.Prime.dvd_mul hp5, or_assoc] at h5
    rcases h5 with h1 | h1 | h1 | h1
    · exact absurd h1 (kgC31Ord_not_dvd_pow_two_pow hp5 (by norm_num) f 12)
    · exact absurd h1 (kgC31Ord_not_five_dvd_pow_eight_add f)
    · exact kgC31Ord_two_dvd_of_five_dvd_pow_six f h1
    · exact kgC31Ord_two_dvd_of_five_dvd_pow_two f h1
  omega

theorem kgC31Ord_fifteen_dvd_of_F4_order (f : ℕ)
    (h : 443520 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1)
      * (2 ^ f - 1)) :
    15 ∣ f := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have h7 : 7 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1)
      * (2 ^ f - 1) := dvd_trans (by norm_num) h
  have h11 : 11 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1)
      * (2 ^ f - 1) := dvd_trans (by norm_num) h
  have h3f : 3 ∣ f := by
    simp only [Nat.Prime.dvd_mul hp7, or_assoc] at h7
    rcases h7 with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 (kgC31Ord_not_dvd_pow_two_pow hp7 (by norm_num) f 12)
    · exact absurd h1 (kgC31Ord_not_seven_dvd_pow_six_add_one f)
    · exact kgC31Ord_three_dvd_of_seven_dvd_pow_four_sub_one f h1
    · exact absurd h1 (kgC31Ord_not_seven_dvd_pow_three_add_one f)
    · exact kgC31Ord_three_dvd_of_seven_dvd_two_pow_sub_one f h1
  have h5f : 5 ∣ f := by
    simp only [Nat.Prime.dvd_mul hp11, or_assoc] at h11
    rcases h11 with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 (kgC31Ord_not_dvd_pow_two_pow hp11 (by norm_num) f 12)
    · exact absurd h1 (kgC31Ord_not_eleven_dvd_pow_six_add_one f)
    · exact kgC31Ord_five_dvd_of_eleven_dvd_pow_four_sub_one f h1
    · exact kgC31Ord_five_dvd_of_eleven_dvd_pow_three_add_one f h1
    · exact kgC31Ord_five_dvd_of_eleven_dvd_two_pow_sub_one f h1
  omega

end CFSG.Quasithin.KGC31

end
