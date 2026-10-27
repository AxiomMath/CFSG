module

public import CFSG.Quasithin.Vol2.Ch11SecBDerived35L2
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem two_pow_le_succ_of_dvd {m N p : ℕ} (hm : 1 ≤ m) (hp : Odd p) (hp3 : 3 ≤ p)
    (hdvd : 2 ^ m ∣ N) (h : 2 * N = p * (p ^ 2 - 1)) : 2 ^ m ≤ p + 1 := by
  obtain ⟨r, rfl⟩ := hp
  have hr : 1 ≤ r := by omega
  have hsq : (2 * r + 1) ^ 2 - 1 = 4 * (r * (r + 1)) := by
    have : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
    omega
  rw [hsq] at h
  have hN : N = 2 * ((2 * r + 1) * (r * (r + 1))) := by nlinarith
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [hN, pow_succ, mul_comm (2 ^ m') 2] at hdvd
  have h3 : 2 ^ m' ∣ (2 * r + 1) * (r * (r + 1)) := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
  have hodd : Odd (2 * r + 1) := ⟨r, rfl⟩
  have h4 : 2 ^ m' ∣ r * (r + 1) :=
    (Nat.Coprime.pow_left m' (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_left h3
  rcases Nat.even_or_odd r with hre | hro
  · have hc : Nat.Coprime (2 ^ m') (r + 1) :=
      Nat.Coprime.pow_left m' (Nat.coprime_two_left.mpr (Even.add_one hre))
    have h5 : 2 ^ m' ≤ r := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h4)
    rw [pow_succ]
    omega
  · have hc : Nat.Coprime (2 ^ m') r := Nat.Coprime.pow_left m' (Nat.coprime_two_left.mpr hro)
    have h5 : 2 ^ m' ≤ r + 1 := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h4)
    rw [pow_succ]
    omega

theorem le_of_two_pow_dvd {m N p : ℕ} (hm : 1 ≤ m) (hp : Odd p) (hp3 : 3 ≤ p)
    (hdvd : 2 ^ m ∣ N) (h : 2 * N = p * (p ^ 2 - 1)) :
    (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m ≤ 2 * N := by
  have hs := two_pow_le_succ_of_dvd hm hp hp3 hdvd h
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have : p ^ 2 = (p - 1) * (p + 1) + 1 := by
      obtain ⟨t, rfl⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  rw [h, hsq]
  calc (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m ≤ (p - 1) * p * (p + 1) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hs
    _ = p * ((p - 1) * (p + 1)) := by ring

theorem sq_eq_succ_mul_pred (x : ℕ) (hx : 1 ≤ x) : x ^ 2 = (x + 1) * (x - 1) + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 1 := ⟨x - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem lt_of_lt_sub_two {X A : ℕ} (h : 2 * A < X - 2) (hX : 2 ≤ X) :
    2 * (X * (A * (X - 1))) < (X - 2) * (X - 1) * X := by
  have h1 : 0 < (X - 1) * X := Nat.mul_pos (by omega) (by omega)
  calc 2 * (X * (A * (X - 1))) = (2 * A) * ((X - 1) * X) := by ring
    _ < (X - 2) * ((X - 1) * X) := Nat.mul_lt_mul_of_pos_right h h1
    _ = (X - 2) * (X - 1) * X := by ring

theorem lt_of_lt_sub_two' {X A : ℕ} (h : 2 * (A * (X + 1)) < (X - 2) * (X - 1)) (hX : 2 ≤ X) :
    2 * (X * (A * (X + 1))) < (X - 2) * (X - 1) * X := by
  calc 2 * (X * (A * (X + 1))) = 2 * (A * (X + 1)) * X := by ring
    _ < (X - 2) * (X - 1) * X := Nat.mul_lt_mul_of_pos_right h (by omega)

theorem prod_Icc_two_three (f : ℕ → ℕ) : ∏ i ∈ Finset.Icc 2 3, f i = f 2 * f 3 := by
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem prod_Icc_one_two (f : ℕ → ℕ) : ∏ i ∈ Finset.Icc 1 2, f i = f 1 * f 2 := by
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]

theorem false_of_isPSL3_of_card {Y : Type} [Group Y] {k p : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 3 2 k Y) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : 2 * Nat.card Y = p * (p ^ 2 - 1)) : False := by
  have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hY).1 rfl
  set q := 2 ^ k with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [show (3 : ℕ) - 1 = 2 from rfl, ordA, show 2 * (2 + 1) / 2 = 3 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, prod_Icc_two_three] at hN
  have hd : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have h1 : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    exact (Nat.gcd_dvd_right 3 (q - 1)).trans (h1.trans (Dvd.intro _ rfl))
  rw [Nat.mul_div_assoc _ hd] at hN
  have hdvd : 2 ^ (3 * k) ∣ Nat.card Y := by
    rw [hN, pow_mul', ← hq]
    exact Dvd.intro _ rfl
  have hle := le_of_two_pow_dvd (by omega) (hp.odd_of_ne_two hp2) (by
    have := hp.two_le; omega) hdvd hcard
  have hup : Nat.card Y ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [hN]
    exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  have hq3 : q ^ 3 = q * q ^ 2 := by ring
  have h4 : 4 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq4
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hlt := lt_of_lt_sub_two (X := q ^ 3) (A := q ^ 2 - 1) (by omega) (by omega)
  rw [pow_mul', ← hq] at hle
  omega

theorem false_of_isPSp4_of_card {Y : Type} [Group Y] {k p : ℕ} (hk : 2 ≤ k)
    (hY : IsPSp4 2 k Y) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : 2 * Nat.card Y = p * (p ^ 2 - 1)) : False := by
  have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hY).2.2.1 rfl
  set q := 2 ^ k with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hgcd : Nat.gcd 2 (q - 1) = 1 := by
    have : Odd (q - 1) := by
      rw [hq]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (by
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)) odd_one
    exact Nat.coprime_two_left.mpr this
  rw [ordBC, show 2 * 2 = 4 from rfl, prod_Icc_one_two, hgcd, Nat.div_one,
    show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl] at hN
  have hdvd : 2 ^ (4 * k) ∣ Nat.card Y := by
    rw [hN, pow_mul', ← hq]
    exact Dvd.intro _ rfl
  have hle := le_of_two_pow_dvd (by omega) (hp.odd_of_ne_two hp2) (by
    have := hp.two_le; omega) hdvd hcard
  have hq4' : q ^ 4 = q ^ 2 * q ^ 2 := by ring
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have h4 : 16 * q ^ 2 ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hq2
  have hlt := lt_of_lt_sub_two (X := q ^ 4) (A := q ^ 2 - 1) (by omega) (by omega)
  rw [pow_mul', ← hq] at hle
  rw [hN] at hcard
  omega

theorem false_of_isPSU3_of_card {Y : Type} [Group Y] {k p : ℕ} (hk : 2 ≤ k)
    (hY : IsPSU 3 2 k Y) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : 2 * Nat.card Y = p * (p ^ 2 - 1)) : False := by
  have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hY).2.1 rfl
  set q := 2 ^ k with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have h1 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    rw [show ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q ^ 2)]; ring]
    exact Int.toNat_natCast _
  have h2 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [ordTwistedA, show (3 : ℕ) - 1 = 2 from rfl, show 2 * (2 + 1) / 2 = 3 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl] at hN
  rw [show (∏ i ∈ Finset.Icc 2 3, ((q : ℤ) ^ i - (-1) ^ i).toNat) =
      ((q : ℤ) ^ 2 - (-1) ^ 2).toNat * ((q : ℤ) ^ 3 - (-1) ^ 3).toNat from
      prod_Icc_two_three _, h1, h2] at hN
  have hd : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have h3 : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by
      have := sq_eq_succ_mul_pred q (by omega)
      omega⟩
    exact (Nat.gcd_dvd_right 3 (q + 1)).trans (h3.trans (Dvd.intro _ rfl))
  rw [Nat.mul_div_assoc _ hd] at hN
  have hdvd : 2 ^ (3 * k) ∣ Nat.card Y := by
    rw [hN, pow_mul', ← hq]
    exact Dvd.intro _ rfl
  have hle := le_of_two_pow_dvd (by omega) (hp.odd_of_ne_two hp2) (by
    have := hp.two_le; omega) hdvd hcard
  have hup : Nat.card Y ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [hN]
    exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  have hkey : 2 * ((q ^ 2 - 1) * (q ^ 3 + 1)) < (q ^ 3 - 2) * (q ^ 3 - 1) := by
    have hq3 : 64 ≤ q ^ 3 := by nlinarith
    zify [(by omega : 1 ≤ q ^ 2), (by omega : 2 ≤ q ^ 3), (by omega : 1 ≤ q ^ 3)]
    have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq4
    nlinarith [mul_le_mul_of_nonneg_left hq' (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ 5),
      mul_le_mul_of_nonneg_left hq' (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ 4)]
  have hlt := lt_of_lt_sub_two' (X := q ^ 3) (A := q ^ 2 - 1) hkey (by nlinarith)
  rw [pow_mul', ← hq] at hle
  omega

theorem false_of_isSz_of_card
    {Y : Type} [Group Y] {k p : ℕ} (hk : 2 ≤ k)
    (hY : IsSz k Y) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : 2 * Nat.card Y = p * (p ^ 2 - 1)) : False := by
  obtain ⟨-, a, -, K, _, _, hka, hK, ⟨e⟩⟩ := hY
  have hN : Nat.card Y = (2 ^ k) ^ 2 * (2 ^ k - 1) * ((2 ^ k) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, hka]
    exact CFSG.LieType.Ree.suzuki_order (by rw [hK, hka])
  set q := 2 ^ k with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hN' : Nat.card Y = q ^ 2 * ((q - 1) * (q ^ 2 + 1)) := by rw [hN]; ring
  have hdvd : 2 ^ (2 * k) ∣ Nat.card Y := by
    rw [hN', pow_mul', ← hq]
    exact Dvd.intro _ rfl
  have hle := le_of_two_pow_dvd (by omega) (hp.odd_of_ne_two hp2) (by
    have := hp.two_le; omega) hdvd hcard
  have hkey : 2 * ((q - 1) * (q ^ 2 + 1)) < (q ^ 2 - 2) * (q ^ 2 - 1) := by
    zify [(by omega : 1 ≤ q), (by omega : 2 ≤ q ^ 2), (by omega : 1 ≤ q ^ 2)]
    have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq4
    nlinarith [mul_le_mul_of_nonneg_left hq' (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ 3),
      mul_le_mul_of_nonneg_left hq' (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ 2)]
  have hlt := lt_of_lt_sub_two' (X := q ^ 2) (A := q - 1) hkey (by omega)
  rw [pow_mul', ← hq] at hle
  rw [hN'] at hcard
  omega

theorem false_of_l2BadType_of_card
    {Y : Type} [Group Y] {k p : ℕ} (hk : 2 ≤ k)
    (hY : L2BadType k Y) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : 2 * Nat.card Y = p * (p ^ 2 - 1)) : False := by
  rcases hY with h | h | h | h
  · exact false_of_isSz_of_card hk h hp hp2 hcard
  · exact false_of_isPSU3_of_card hk h hp hp2 hcard
  · exact false_of_isPSL3_of_card hk h hp hp2 hcard
  · have h' : IsPSp4 2 k Y := by
      unfold E2.IsSp4Prime at h
      split_ifs at h with hk1
      · omega
      · exact h
    exact false_of_isPSp4_of_card hk h' hp hp2 hcard

end CFSG.Quasithin.Vol2.Ch11.SecB
