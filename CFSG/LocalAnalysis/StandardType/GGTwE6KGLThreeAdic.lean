module

public import CFSG.Open.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
import CFSG.HardMathSupport.Malle.Proving.E27OrderModTwo
import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open

section LTE

variable {x : ℕ}

private theorem sq_sub_one_eq_3k (hx : 1 ≤ x) : x ^ 2 - 1 = (x + 1) * (x - 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  zify [hx, h2]
  ring

private theorem padicValNat_pow_sub_one_even_3k (hx : 3 ∣ x + 1) (hx2 : 2 ≤ x) {d i : ℕ}
    (hd : d = 2 * i) (hi : i ≠ 0) :
    padicValNat 3 (x ^ d - 1) = padicValNat 3 (x + 1) + padicValNat 3 i := by
  subst hd
  have hx1 : 1 ≤ x := by omega
  have hlt : 1 < x ^ 2 := by nlinarith
  have hdvd : 3 ∣ x ^ 2 - 1 := by
    rw [sq_sub_one_eq_3k hx1]
    exact hx.mul_right _
  have hnd : ¬ 3 ∣ x ^ 2 := fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h := padicValNat.pow_sub_pow (p := 3) (x := x ^ 2) (y := 1) (by decide) hlt hdvd hnd hi
  rw [one_pow, ← pow_mul] at h
  rw [h, sq_sub_one_eq_3k hx1, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (show ¬ 3 ∣ x - 1 by omega), add_zero]

private theorem padicValNat_pow_odd_sub_one_3k (hx : 3 ∣ x + 1) {k : ℕ} (hk : Odd k) :
    padicValNat 3 (x ^ k - 1) = 0 := by
  obtain ⟨m, rfl⟩ := hk
  have hx2 : x % 3 = 2 := by omega
  have h : x ^ (2 * m + 1) % 3 = 2 := by
    rw [Nat.pow_mod, hx2, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  refine padicValNat.eq_zero_of_not_dvd ?_
  generalize x ^ (2 * m + 1) = z at h ⊢
  omega

private theorem padicValNat_pow_3k (hx : 3 ∣ x + 1) (k : ℕ) : padicValNat 3 (x ^ k) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega

private theorem pow_sub_one_ne_zero_3k (hx2 : 2 ≤ x) {k : ℕ} (hk : k ≠ 0) : x ^ k - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hk (by omega))

private theorem padicValNat_small_3k :
    padicValNat 3 1 = 0 ∧ padicValNat 3 2 = 0 ∧ padicValNat 3 3 = 1 ∧ padicValNat 3 4 = 0 ∧
      padicValNat 3 6 = 1 := by
  have h2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h3 : padicValNat 3 3 = 1 := padicValNat.self (by norm_num)
  have h6 : padicValNat 3 (2 * 3) = padicValNat 3 2 + padicValNat 3 3 :=
    padicValNat.mul (by norm_num) (by norm_num)
  rw [h2, h3] at h6
  exact ⟨padicValNat.one, h2, h3, padicValNat.eq_zero_of_not_dvd (by norm_num), by simpa using h6⟩

end LTE

theorem padicValNat_three_ordD_four {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (ordD 4 q) = 4 * padicValNat 3 (q + 1) + 1 := by
  obtain ⟨v1, v2, v3, -, -⟩ := padicValNat_small_3k
  have hodd : Odd (q ^ 4 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hq.pow_of_ne_zero (by norm_num)) odd_one
  have hg : Nat.gcd 4 (q ^ 4 - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd))
  have h12 : q ^ 12 ≠ 0 := pow_ne_zero _ (by omega)
  have h4 := pow_sub_one_ne_zero_3k hq2 (k := 4) (by norm_num)
  have h2 := pow_sub_one_ne_zero_3k hq2 (k := 2) (by norm_num)
  have h6 := pow_sub_one_ne_zero_3k hq2 (k := 6) (by norm_num)
  rw [ordD, hg, Nat.div_one, show Finset.Icc 1 (4 - 1) = ({1, 2, 3} : Finset ℕ) from rfl,
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)]
  show padicValNat 3 (q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1)))) = _
  rw [padicValNat.mul (mul_ne_zero h12 h4) (mul_ne_zero h2 (mul_ne_zero h4 h6)),
    padicValNat.mul h12 h4, padicValNat.mul h2 (mul_ne_zero h4 h6), padicValNat.mul h4 h6,
    padicValNat_pow_3k h3,
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 4) (i := 2) rfl (by norm_num),
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 2) (i := 1) rfl (by norm_num),
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 6) (i := 3) rfl (by norm_num), v1, v2, v3]
  ring

private theorem padicValNat_three_ordE6_3k {q : ℕ} (hq2 : 2 ≤ q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (ordE6 q) = 4 * padicValNat 3 (q + 1) + 2 := by
  obtain ⟨v1, -, v3, v4, v6⟩ := padicValNat_small_3k
  have hg : Nat.gcd 3 (q - 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have h36 : q ^ 36 ≠ 0 := pow_ne_zero _ (by omega)
  have h12 := pow_sub_one_ne_zero_3k hq2 (k := 12) (by norm_num)
  have h9 := pow_sub_one_ne_zero_3k hq2 (k := 9) (by norm_num)
  have h8 := pow_sub_one_ne_zero_3k hq2 (k := 8) (by norm_num)
  have h6 := pow_sub_one_ne_zero_3k hq2 (k := 6) (by norm_num)
  have h5 := pow_sub_one_ne_zero_3k hq2 (k := 5) (by norm_num)
  have h2 := pow_sub_one_ne_zero_3k hq2 (k := 2) (by norm_num)
  have n1 := mul_ne_zero h36 h12
  have n2 := mul_ne_zero n1 h9
  have n3 := mul_ne_zero n2 h8
  have n4 := mul_ne_zero n3 h6
  have n5 := mul_ne_zero n4 h5
  rw [ordE6, hg, Nat.div_one, padicValNat.mul n5 h2, padicValNat.mul n4 h5, padicValNat.mul n3 h6,
    padicValNat.mul n2 h8, padicValNat.mul n1 h9, padicValNat.mul h36 h12, padicValNat_pow_3k h3,
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 12) (i := 6) rfl (by norm_num),
    padicValNat_pow_odd_sub_one_3k h3 (k := 9) (by decide),
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 8) (i := 4) rfl (by norm_num),
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 6) (i := 3) rfl (by norm_num),
    padicValNat_pow_odd_sub_one_3k h3 (k := 5) (by decide),
    padicValNat_pow_sub_one_even_3k h3 hq2 (d := 2) (i := 1) rfl (by norm_num), v1, v3, v4, v6]
  ring

private theorem odd_of_three_dvd_3k {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · exfalso
    have h4 : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · exact hn

private theorem setup_3k {g m : ℕ} (hgm : g ∣ m) (hm : Odd m) :
    2 ≤ 2 ^ g ∧ 3 ∣ 2 ^ g + 1 ∧ Even (2 ^ m) ∧ 2 ≤ 2 ^ m ∧ 3 ∣ 2 ^ m + 1 ∧
      padicValNat 3 (2 ^ g + 1) ≤ padicValNat 3 (2 ^ m + 1) := by
  obtain ⟨c, rfl⟩ := hgm
  have hc : Odd c := (Nat.odd_mul.mp hm).2
  have hg : Odd g := (Nat.odd_mul.mp hm).1
  have hq3 : 3 ∣ 2 ^ g + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hg
  have hQ3 : 3 ∣ 2 ^ (g * c) + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hm
  have hqQ : 2 ^ g + 1 ∣ 2 ^ (g * c) + 1 := by
    rw [pow_mul]
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ g) 1 hc
  refine ⟨?_, hq3, even_two.pow_of_ne_zero hm.pos.ne', ?_, hQ3, ?_⟩
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right two_pos hg.pos
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (g * c) := Nat.pow_le_pow_right two_pos hm.pos
  · exact (padicValNat_dvd_iff_le (p := 3) (Nat.add_one_ne_zero _)).mp
      ((pow_padicValNat_dvd (p := 3)).trans hqQ)

theorem padicValNat_three_ordF4_le_ordD_four {g n : ℕ} (hgn : g ∣ n) (hn : 3 ∣ 2 ^ n + 1) :
    padicValNat 3 (ordF4 (2 ^ g)) ≤ padicValNat 3 (ordD 4 (2 ^ n)) + 1 := by
  obtain ⟨hq2, hq3, hQe, hQ2, -, hab⟩ := setup_3k hgn (odd_of_three_dvd_3k hn)
  rw [CFSG.HardMathSupport.Malle.Proving.padicValNat_three_ordF4_of_mod_two (by omega) (by omega),
    padicValNat_three_ordD_four hQe hQ2 hn]
  omega

theorem padicValNat_three_ordE6_le_ordD_four {g n : ℕ} (hgn : g ∣ n) (hn : 3 ∣ 2 ^ n + 1) :
    padicValNat 3 (ordE6 (2 ^ g)) ≤ padicValNat 3 (ordD 4 (2 ^ n)) + 1 := by
  obtain ⟨hq2, hq3, hQe, hQ2, -, hab⟩ := setup_3k hgn (odd_of_three_dvd_3k hn)
  rw [padicValNat_three_ordE6_3k hq2 hq3, padicValNat_three_ordD_four hQe hQ2 hn]
  omega

end CFSG.StandardType.SCFourCover

end
