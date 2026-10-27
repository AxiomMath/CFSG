module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepOrdB
public import CFSG.Quasithin.Background.B69Num

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace B69

namespace E22FamC

variable {F : Type} [Group F] {x k : ℕ} (hx4 : 4 ≤ x) (hx6 : x ^ 6 = 2 ^ k)
  (hd : 2 ^ k ∣ Nat.card F) (hle : Nat.card F ≤ x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)))
include hx4 hx6 hd hle

theorem g2_psl2 {p e : ℕ} (hp : IsPSL 2 p e F) : False := by
  have h1 := card_psl_two_mul hp
  have hQ2 : 2 ≤ p ^ e := by
    have h1p := hp.1.1.two_le
    have := hp.1.2.1
    calc 2 ≤ p := h1p
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) this
  set Q := p ^ e with hQdef
  have hg : Nat.gcd 2 (Q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hQ : x ^ 6 ≤ Q + 1 := by
    rcases Nat.even_or_odd Q with hev | hodd
    · have hg1 : Nat.gcd 2 (Q - 1) = 1 := by
        have hod : Odd (Q - 1) := Nat.Even.sub_odd (by omega) hev odd_one
        exact Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hod)
      rw [hg1] at h1
      have hF3 : Nat.card F = Q * (Q ^ 2 - 1) := by
        have : Q ^ 3 = Q * Q ^ 2 := by ring
        have h4 : Q * (Q ^ 2 - 1) = Q * Q ^ 2 - Q := by rw [Nat.mul_sub, mul_one]
        omega
      have hod2 : Odd (Q ^ 2 - 1) :=
        Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hev.pow_of_ne_zero (by norm_num))
          odd_one
      rw [hF3] at hd
      have := Nat.le_of_dvd (by omega) (two_pow_dvd_of_odd_mul hod2 hd)
      rw [hx6]
      omega
    · have hg2 : Nat.gcd 2 (Q - 1) = 2 := by
        apply Nat.gcd_eq_left
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
      rw [hg2] at h1
      have hF3 : Nat.card F * 2 = Q * (Q ^ 2 - 1) := by
        have : Q ^ 3 = Q * Q ^ 2 := by ring
        have h4 : Q * (Q ^ 2 - 1) = Q * Q ^ 2 - Q := by rw [Nat.mul_sub, mul_one]
        omega
      have hd2 : 2 ^ (k + 1) ∣ Q * (Q ^ 2 - 1) := by
        rw [← hF3, pow_succ]
        exact Nat.mul_dvd_mul hd (dvd_refl 2)
      have hd3 := two_pow_dvd_of_odd_mul' hodd hd2
      have := le_of_two_pow_dvd_sq_sub_one hodd (by omega) hd3
      rw [hx6]
      exact this
  have := psl2_ineq hx4 hQ hg h1
  omega

theorem g2_sz {m : ℕ} (hm : IsSz m F) : False := by
  obtain ⟨-, a, ha, F', _, _, hfa, hF', ⟨e⟩⟩ := hm
  have hF'' : Nat.card F' = 2 ^ (2 * a + 1) := by rw [hF', hfa]
  have hc' : Nat.card F = CFSG.Open.ordSuzuki (2 ^ m) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF'', hfa, CFSG.Open.ordSuzuki]
    exact Nat.mul_right_comm _ _ _
  rw [CFSG.Open.ordSuzuki] at hc'
  have hQ8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hev : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  set Q := 2 ^ m with hQdef
  have hod : Odd ((Q ^ 2 + 1) * (Q - 1)) :=
    Odd.mul (Even.add_one (hev.pow_of_ne_zero (by norm_num)))
      (Nat.Even.sub_odd (by omega) hev odd_one)
  have hF3 : Nat.card F = Q ^ 2 * ((Q ^ 2 + 1) * (Q - 1)) := by rw [hc']; ring
  rw [hF3] at hd
  have hd2 := two_pow_dvd_of_odd_mul hod hd
  have h5 : x ^ 6 ≤ Q ^ 2 := by
    rw [hx6]
    exact Nat.le_of_dvd (by positivity) hd2
  have hQx : x ^ 3 ≤ Q := by
    have : (x ^ 3) ^ 2 ≤ Q ^ 2 := by
      calc (x ^ 3) ^ 2 = x ^ 6 := by ring
        _ ≤ Q ^ 2 := h5
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  have := sz_ineq hx4 hQx
  rw [hc'] at hle
  omega

theorem g2_psu_two {m : ℕ} (hm : IsPSU 3 2 m F) :
    False := by
  have hn2 : 2 ≤ m := by
    obtain ⟨-, hf, -, h32⟩ := hm.1
    by_contra hlt
    have : m = 1 := by omega
    subst this
    exact h32 (by norm_num)
  have h1 := card_psu_three_mul hm
  have hg : Nat.gcd 3 (2 ^ m + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hQ4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hn2
  have hev : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  set Q := 2 ^ m with hQdef
  have hod : Odd ((Q ^ 2 - 1) * (Q ^ 3 + 1)) :=
    Odd.mul (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hev.pow_of_ne_zero (by norm_num))
      odd_one) (Even.add_one (hev.pow_of_ne_zero (by norm_num)))
  have hd2 : 2 ^ k ∣ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
    rw [← h1]
    exact Dvd.dvd.mul_right hd _
  have h5 : x ^ 6 ≤ Q ^ 3 := by
    rw [hx6]
    exact Nat.le_of_dvd (by positivity) (two_pow_dvd_of_odd_mul hod hd2)
  have hQx : x ^ 2 ≤ Q := by
    have : (x ^ 2) ^ 3 ≤ Q ^ 3 := by
      calc (x ^ 2) ^ 3 = x ^ 6 := by ring
        _ ≤ Q ^ 3 := h5
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  have := unit_ineq hx4 hQx hg (Or.inl h1)
  omega

end E22FamC

end B69

end CFSG.Quasithin
