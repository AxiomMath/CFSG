module

public import CFSG.Open.Defs
import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open

section LTE

variable {x : ℕ}

private theorem sq_sub_one_eq_3a (hx : 1 ≤ x) : x ^ 2 - 1 = (x + 1) * (x - 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  zify [hx, h2]
  ring

private theorem padicValNat_pow_two_mul_sub_one_3a (hx : 3 ∣ x + 1) (hx2 : 2 ≤ x) {i : ℕ}
    (hi : i ≠ 0) :
    padicValNat 3 (x ^ (2 * i) - 1) = padicValNat 3 (x + 1) + padicValNat 3 i := by
  have hx1 : 1 ≤ x := by omega
  have hlt : 1 < x ^ 2 := by nlinarith
  have hdvd : 3 ∣ x ^ 2 - 1 := by
    rw [sq_sub_one_eq_3a hx1]
    exact hx.mul_right _
  have hnd : ¬ 3 ∣ x ^ 2 := fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h := padicValNat.pow_sub_pow (p := 3) (x := x ^ 2) (y := 1) (by decide) hlt hdvd hnd hi
  rw [one_pow, ← pow_mul] at h
  rw [h, sq_sub_one_eq_3a hx1, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (show ¬ 3 ∣ x - 1 by omega), add_zero]

private theorem padicValNat_pow_add_one_3a (hx : 3 ∣ x + 1) {k : ℕ} (hk : Odd k) :
    padicValNat 3 (x ^ k + 1) = padicValNat 3 (x + 1) + padicValNat 3 k := by
  have h := padicValNat.pow_add_pow (p := 3) (x := x) (y := 1) (by decide) hx (by omega) hk
  rwa [one_pow] at h

private theorem padicValNat_pow_3a (hx : 3 ∣ x + 1) (k : ℕ) : padicValNat 3 (x ^ k) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega

private theorem pow_two_mul_sub_one_ne_zero_3a (hx2 : 2 ≤ x) {i : ℕ} (hi : i ≠ 0) :
    x ^ (2 * i) - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega))

private theorem padicValNat_small_3a :
    padicValNat 3 1 = 0 ∧ padicValNat 3 2 = 0 ∧ padicValNat 3 3 = 1 ∧ padicValNat 3 4 = 0 ∧
      padicValNat 3 5 = 0 :=
  ⟨padicValNat.one, padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)⟩

private theorem padicValNat_mul_six_3a {a b c d e f : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    padicValNat 3 (a * (b * (c * (d * (e * f))))) = padicValNat 3 a + padicValNat 3 b +
      padicValNat 3 c + padicValNat 3 d + padicValNat 3 e + padicValNat 3 f := by
  rw [padicValNat.mul ha (mul_ne_zero hb (mul_ne_zero hc (mul_ne_zero hd (mul_ne_zero he hf)))),
    padicValNat.mul hb (mul_ne_zero hc (mul_ne_zero hd (mul_ne_zero he hf))),
    padicValNat.mul hc (mul_ne_zero hd (mul_ne_zero he hf)), padicValNat.mul hd (mul_ne_zero he hf),
    padicValNat.mul he hf]
  ring

end LTE

private theorem toNat_even_3a {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [this]; ring
  rw [h, Int.toNat_natCast]

private theorem toNat_odd_3a {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  have h : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private theorem ordBC_five_eq_3a {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    ordBC 5 q = q ^ (5 * 5) * ((q ^ (2 * 1) - 1) * ((q ^ (2 * 2) - 1) * ((q ^ (2 * 3) - 1) *
      ((q ^ (2 * 4) - 1) * (q ^ (2 * 5) - 1))))) := by
  rw [ordBC, Nat.coprime_two_left.mpr (Nat.Even.sub_odd (by omega) hq odd_one), Nat.div_one,
    show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) from rfl, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)]

private theorem ordTwistedD_five_eq_3a {q : ℕ} (hq : Even q) :
    ordTwistedD 5 q = q ^ (5 * (5 - 1)) * ((q ^ 5 + 1) * ((q ^ (2 * 1) - 1) *
      ((q ^ (2 * 2) - 1) * ((q ^ (2 * 3) - 1) * (q ^ (2 * 4) - 1))))) := by
  have hodd : Odd (q ^ 5 + 1) := (hq.pow_of_ne_zero (by norm_num)).add_one
  have hg : Nat.gcd 4 (q ^ 5 + 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd))
  rw [ordTwistedD, hg, Nat.div_one, show Finset.Icc 1 (5 - 1) = ({1, 2, 3, 4} : Finset ℕ) from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    mul_assoc]

private theorem ordTwistedA_five_mul_3a {Q : ℕ} (hQ : 1 ≤ Q) :
    ordTwistedA 5 Q * Nat.gcd 6 (Q + 1) = Q ^ 15 * ((Q ^ (2 * 1) - 1) * ((Q ^ 3 + 1) *
      ((Q ^ (2 * 2) - 1) * ((Q ^ 5 + 1) * (Q ^ (2 * 3) - 1))))) := by
  have h3 : Q + 1 ∣ Q ^ 3 + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow Q 1 (by decide : Odd 3)
  rw [ordTwistedA, show Finset.Icc 2 (5 + 1) = ({2, 3, 4, 5, 6} : Finset ℕ) from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num), toNat_even_3a hQ (by decide), toNat_odd_3a (by decide),
    toNat_even_3a hQ (by decide), toNat_odd_3a (by decide), toNat_even_3a hQ (by decide),
    show 5 * (5 + 1) / 2 = 15 from rfl, show (5 : ℕ) + 1 = 6 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _) _))

theorem padicValNat_ordBC_five {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) (h3 : 3 ∣ q + 1) :
    ordBC 5 q ≠ 0 ∧ padicValNat 3 (ordBC 5 q) = 5 * padicValNat 3 (q + 1) + 1 := by
  obtain ⟨h1, h2, h3', h4, h5⟩ := padicValNat_small_3a
  have hz := fun {i : ℕ} (hi : i ≠ 0) => pow_two_mul_sub_one_ne_zero_3a hq2 hi
  have hv := fun {i : ℕ} (hi : i ≠ 0) => padicValNat_pow_two_mul_sub_one_3a h3 hq2 hi
  have hq0 : q ^ (5 * 5) ≠ 0 := pow_ne_zero _ (by omega)
  have h5' : (5 : ℕ) ≠ 0 := by norm_num
  rw [ordBC_five_eq_3a hq hq2]
  refine ⟨mul_ne_zero hq0 (mul_ne_zero (hz one_ne_zero) (mul_ne_zero (hz two_ne_zero)
    (mul_ne_zero (hz three_ne_zero) (mul_ne_zero (hz four_ne_zero) (hz h5'))))), ?_⟩
  rw [padicValNat_mul_six_3a hq0 (hz one_ne_zero) (hz two_ne_zero) (hz three_ne_zero)
    (hz four_ne_zero) (hz h5'), padicValNat_pow_3a h3, hv one_ne_zero, hv two_ne_zero,
    hv three_ne_zero, hv four_ne_zero, hv h5', h1, h2, h3', h4, h5]
  ring

theorem padicValNat_ordTwistedD_five {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) (h3 : 3 ∣ q + 1) :
    ordTwistedD 5 q ≠ 0 ∧ padicValNat 3 (ordTwistedD 5 q) = 5 * padicValNat 3 (q + 1) + 1 := by
  obtain ⟨h1, h2, h3', h4, h5⟩ := padicValNat_small_3a
  have hz := fun {i : ℕ} (hi : i ≠ 0) => pow_two_mul_sub_one_ne_zero_3a hq2 hi
  have hv := fun {i : ℕ} (hi : i ≠ 0) => padicValNat_pow_two_mul_sub_one_3a h3 hq2 hi
  have hq0 : q ^ (5 * (5 - 1)) ≠ 0 := pow_ne_zero _ (by omega)
  have h50 : q ^ 5 + 1 ≠ 0 := by omega
  rw [ordTwistedD_five_eq_3a hq]
  refine ⟨mul_ne_zero hq0 (mul_ne_zero h50 (mul_ne_zero (hz one_ne_zero) (mul_ne_zero
    (hz two_ne_zero) (mul_ne_zero (hz three_ne_zero) (hz four_ne_zero))))), ?_⟩
  rw [padicValNat_mul_six_3a hq0 h50 (hz one_ne_zero) (hz two_ne_zero) (hz three_ne_zero)
    (hz four_ne_zero), padicValNat_pow_3a h3, padicValNat_pow_add_one_3a h3 (by decide),
    hv one_ne_zero, hv two_ne_zero, hv three_ne_zero, hv four_ne_zero, h1, h2, h3', h4, h5]
  ring

theorem padicValNat_ordTwistedA_five {Q : ℕ} (hQ2 : 2 ≤ Q) (h3 : 3 ∣ Q + 1) :
    ordTwistedA 5 Q ≠ 0 ∧ padicValNat 3 (ordTwistedA 5 Q) = 5 * padicValNat 3 (Q + 1) + 1 := by
  obtain ⟨-, h2, h3', -, h5⟩ := padicValNat_small_3a
  have hz := fun {i : ℕ} (hi : i ≠ 0) => pow_two_mul_sub_one_ne_zero_3a hQ2 hi
  have hv := fun {i : ℕ} (hi : i ≠ 0) => padicValNat_pow_two_mul_sub_one_3a h3 hQ2 hi
  have hQ0 : Q ^ 15 ≠ 0 := pow_ne_zero _ (by omega)
  have h30 : Q ^ 3 + 1 ≠ 0 := by omega
  have h50 : Q ^ 5 + 1 ≠ 0 := by omega
  have he := ordTwistedA_five_mul_3a (Q := Q) (by omega)
  have hP0 : ordTwistedA 5 Q * Nat.gcd 6 (Q + 1) ≠ 0 := by
    rw [he]
    exact mul_ne_zero hQ0 (mul_ne_zero (hz one_ne_zero) (mul_ne_zero h30 (mul_ne_zero
      (hz two_ne_zero) (mul_ne_zero h50 (hz three_ne_zero)))))
  have hU0 : ordTwistedA 5 Q ≠ 0 := left_ne_zero_of_mul hP0
  have hd0 : Nat.gcd 6 (Q + 1) ≠ 0 := right_ne_zero_of_mul hP0
  have hd : padicValNat 3 (Nat.gcd 6 (Q + 1)) = 1 := by
    have hlo : 3 ^ 1 ∣ Nat.gcd 6 (Q + 1) := Nat.dvd_gcd (by norm_num) (by simpa using h3)
    have hhi : ¬ 3 ^ 2 ∣ Nat.gcd 6 (Q + 1) := fun h => by
      have := h.trans (Nat.gcd_dvd_left 6 (Q + 1))
      norm_num at this
    have := (padicValNat_dvd_iff_le hd0).mp hlo
    have := mt (padicValNat_dvd_iff_le hd0).mpr hhi
    omega
  have hval := congrArg (padicValNat 3) he
  rw [padicValNat.mul hU0 hd0, hd, padicValNat_mul_six_3a hQ0 (hz one_ne_zero) h30
    (hz two_ne_zero) h50 (hz three_ne_zero), padicValNat_pow_3a h3,
    padicValNat_pow_add_one_3a h3 (by decide), padicValNat_pow_add_one_3a h3 (by decide),
    hv one_ne_zero, hv two_ne_zero, hv three_ne_zero, padicValNat.one, h2, h3', h5] at hval
  exact ⟨hU0, by omega⟩

private theorem odd_of_three_dvd_3a {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · exfalso
    have h4 : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · exact hn

private theorem setup_3a {g n : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (hn : 3 ∣ 2 ^ n + 1) :
    Even (2 ^ g) ∧ 2 ≤ 2 ^ g ∧ 3 ∣ 2 ^ g + 1 ∧ 2 ≤ 2 ^ n ∧
      padicValNat 3 (2 ^ g + 1) ≤ padicValNat 3 (2 ^ n + 1) := by
  have hnodd := odd_of_three_dvd_3a hn
  obtain ⟨c, rfl⟩ := hgn
  have hc : Odd c := (Nat.odd_mul.mp hnodd).2
  have hgodd : Odd g := (Nat.odd_mul.mp hnodd).1
  have hq3 : 3 ∣ 2 ^ g + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hgodd
  have hqQ : 2 ^ g + 1 ∣ 2 ^ (g * c) + 1 := by
    rw [pow_mul]
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ g) 1 hc
  refine ⟨(even_two).pow_of_ne_zero (by omega), ?_, hq3, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right two_pos hg
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (g * c) := Nat.pow_le_pow_right two_pos (by
          have := hc.pos
          nlinarith)
  · exact (padicValNat_dvd_iff_le (p := 3) (Nat.add_one_ne_zero _)).mp
      ((pow_padicValNat_dvd (p := 3)).trans hqQ)

theorem not_three_mul_ordTwistedA_five_dvd_ordBC_five {g n : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hn : 3 ∣ 2 ^ n + 1) : ¬ 3 * ordTwistedA 5 (2 ^ n) ∣ ordBC 5 (2 ^ g) := by
  intro hdvd
  obtain ⟨hqe, hq2, hq3, hQ2, hab⟩ := setup_3a hg hgn hn
  obtain ⟨hR0, hR⟩ := padicValNat_ordBC_five hqe hq2 hq3
  obtain ⟨hU0, hU⟩ := padicValNat_ordTwistedA_five hQ2 hn
  have hle := (padicValNat_dvd_iff_le (p := 3) hR0).mp ((pow_padicValNat_dvd (p := 3)).trans hdvd)
  rw [padicValNat.mul (by norm_num) hU0, padicValNat.self (by norm_num), hU, hR] at hle
  omega

theorem not_three_mul_ordTwistedA_five_dvd_ordTwistedD_five {g n : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n) (hn : 3 ∣ 2 ^ n + 1) : ¬ 3 * ordTwistedA 5 (2 ^ n) ∣ ordTwistedD 5 (2 ^ g) := by
  intro hdvd
  obtain ⟨hqe, hq2, hq3, hQ2, hab⟩ := setup_3a hg hgn hn
  obtain ⟨hR0, hR⟩ := padicValNat_ordTwistedD_five hqe hq2 hq3
  obtain ⟨hU0, hU⟩ := padicValNat_ordTwistedA_five hQ2 hn
  have hle := (padicValNat_dvd_iff_le (p := 3) hR0).mp ((pow_padicValNat_dvd (p := 3)).trans hdvd)
  rw [padicValNat.mul (by norm_num) hU0, padicValNat.self (by norm_num), hU, hR] at hle
  omega

end CFSG.StandardType.SCFourCover

end
