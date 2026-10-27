module

public import CFSG.Quasithin.EmptyFaithful.R3c6Psl
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Open (ordA ordBC)
open CFSG.Quasithin CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X]

theorem two_mul_pow_eight_lt {q : ℕ} (hq : 5 ≤ q) :
    2 * q ^ 8 < (q ^ 3 - 1) * ((q ^ 3 - 1) ^ 2 - 1) := by
  have h125 : 125 ≤ q ^ 3 :=
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  obtain ⟨a, ha⟩ : ∃ a, q ^ 3 = a + 2 := ⟨q ^ 3 - 2, by omega⟩
  have ha123 : 123 ≤ a := by omega
  have hq2 : 5 * q ^ 2 ≤ a + 2 := by
    rw [← ha, show q ^ 3 = q * q ^ 2 by ring]
    exact Nat.mul_le_mul_right _ hq
  have hq8 : q ^ 8 = (a + 2) * (a + 2) * q ^ 2 := by
    rw [← ha]; ring
  have key : 2 * q ^ 2 * (a + 2) < a * (a + 1) := by
    have h1 : 5 * q ^ 2 * (a + 2) ≤ (a + 2) * (a + 2) := Nat.mul_le_mul_right _ hq2
    nlinarith [h1]
  have e1 : a + 2 - 1 = a + 1 := by omega
  have e2 : (a + 1) ^ 2 - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [ha, e1, e2, hq8]
  calc 2 * ((a + 2) * (a + 2) * q ^ 2) = (2 * q ^ 2 * (a + 2)) * (a + 2) := by ring
    _ < (a * (a + 1)) * (a + 2) := Nat.mul_lt_mul_of_pos_right key (by omega)
    _ = (a + 1) * (a * (a + 2)) := by ring

theorem not_isOddOrder_of_prod {N c m : ℕ} (hc0 : 0 < c) (hc : c ≤ 2)
    (hm : ∀ p e : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → ¬ (p ^ e) ^ 3 ∣ m)
    (h : N * c = m * (m ^ 2 - 1)) : ¬ IsOddOrder N := by
  intro hN
  have hNpos := hN.pos
  obtain ⟨p, e, hp, hp5, he, hd, hlt⟩ := hN.exists_prime_power
  have hp2 : p ≠ 2 := by omega
  have hq5 : 5 ≤ p ^ e := hp5.trans (Nat.le_self_pow (by omega) p)
  have hdvd : (p ^ e) ^ 3 ∣ m * (m ^ 2 - 1) := by
    rw [← h]; exact hd.trans (dvd_mul_right N c)
  have hNc : 0 < m * (m ^ 2 - 1) := by rw [← h]; exact Nat.mul_pos hNpos hc0
  have hm2 : 2 ≤ m := by
    by_contra hlt2
    have hlt2' : m < 2 := not_le.mp hlt2
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl <;> simp at hNc
  have hcase : (p ^ e) ^ 3 ∣ m - 1 ∨ (p ^ e) ^ 3 ∣ m + 1 := by
    by_cases hpm : p ∣ m
    · exfalso
      have hpn : ¬ p ∣ m ^ 2 - 1 := by
        intro hpd
        have h1 : p ∣ m ^ 2 := dvd_pow hpm (by norm_num)
        have h2 : m ^ 2 - 1 + 1 = m ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
        have : p ∣ 1 := (Nat.dvd_add_right hpd).1 (h2 ▸ h1)
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      have hcop : Nat.Coprime ((p ^ e) ^ 3) (m ^ 2 - 1) :=
        (((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).pow_left e).pow_left 3
      exact hm p e hp hp2 he (hcop.dvd_of_dvd_mul_right hdvd)
    · have hcop : Nat.Coprime ((p ^ e) ^ 3) m :=
        (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).pow_left e).pow_left 3
      have h1 : (p ^ e) ^ 3 ∣ m ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd
      have hfac : m ^ 2 - 1 = (m + 1) * (m - 1) := by
        have := Nat.sq_sub_sq m 1
        simpa using this
      rw [hfac] at h1
      by_cases hpm1 : p ∣ m - 1
      · have hpm1' : ¬ p ∣ m + 1 := by
          intro hpd
          have h3 : p ∣ (m + 1) - (m - 1) := Nat.dvd_sub hpd hpm1
          have h2 : (m + 1) - (m - 1) = 2 := by omega
          rw [h2] at h3
          have := Nat.le_of_dvd (by norm_num) h3
          omega
        have hcop2 : Nat.Coprime ((p ^ e) ^ 3) (m + 1) :=
          (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm1').pow_left e).pow_left 3
        exact Or.inl (hcop2.dvd_of_dvd_mul_left h1)
      · have hcop2 : Nat.Coprime ((p ^ e) ^ 3) (m - 1) :=
          (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm1).pow_left e).pow_left 3
        exact Or.inr (hcop2.dvd_of_dvd_mul_right h1)
  have hle : (p ^ e) ^ 3 ≤ m + 1 := by
    rcases hcase with hd1 | hd1
    · have := Nat.le_of_dvd (by omega) hd1
      omega
    · exact Nat.le_of_dvd (by omega) hd1
  have hmge : (p ^ e) ^ 3 - 1 ≤ m := by omega
  have h1 := two_mul_pow_eight_lt hq5
  have h2 : ((p ^ e) ^ 3 - 1) * (((p ^ e) ^ 3 - 1) ^ 2 - 1) ≤ m * (m ^ 2 - 1) :=
    Nat.mul_le_mul hmge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hmge 2) 1)
  have h3 : N * c ≤ N * 2 := Nat.mul_le_mul_left N hc
  have h4 : N * 2 < 2 * (p ^ e) ^ 8 := by omega
  omega

section Linear

theorem notOdd_psl3_two {f : ℕ} (hf : 1 ≤ f) (h : IsPSL 3 2 f X) : ¬ IsOddOrder (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := psl3Data h
  have hg : Odd (Nat.gcd 3 (2 ^ f - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have h2 := odd_pow_sub_one hf (a := 2) (by norm_num)
  have h3 := odd_pow_sub_one hf (a := 3) (by norm_num)
  refine notOddOrder_of_two_part hg (h2.mul h3) (a := f * 3) (b := f * 8) ?_ ?_ ?_
  · rw [hN, pow_mul]
  · have e2 : (2 ^ f) ^ 2 - 1 < (2 ^ f) ^ 2 := Nat.sub_lt (by positivity) one_pos
    have e3 : (2 ^ f) ^ 3 - 1 < (2 ^ f) ^ 3 := Nat.sub_lt (by positivity) one_pos
    calc 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1))
        < 2 ^ (f * 3) * ((2 ^ f) ^ 2 * (2 ^ f) ^ 3) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' e2 e3) (by positivity)
      _ = 2 ^ (f * 8) := by ring
  · omega

theorem notOdd_psu3_two {f : ℕ} (hf : 1 ≤ f) (h : IsPSU 3 2 f X) : ¬ IsOddOrder (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := psu3Data h
  have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have h2 := odd_pow_sub_one hf (a := 2) (by norm_num)
  have h3 := odd_pow_add_one hf (a := 3) (by norm_num)
  refine notOddOrder_of_two_part hg (h2.mul h3) (a := f * 3) (b := f * 8) ?_ ?_ ?_
  · rw [hN, pow_mul]
  · have hQ : 2 ≤ 2 ^ f :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have e : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) < (2 ^ f) ^ 2 * (2 ^ f) ^ 3 := by
      have h23 : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      zify [h1]
      nlinarith
    calc 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))
        < 2 ^ (f * 3) * ((2 ^ f) ^ 2 * (2 ^ f) ^ 3) :=
          Nat.mul_lt_mul_of_pos_left e (by positivity)
      _ = 2 ^ (f * 8) := by ring
  · omega

end Linear

section CharTwo

theorem two_pow_mul_lt {f a k r : ℕ} (hr : r < (2 ^ f) ^ k) :
    2 ^ (f * a) * r < 2 ^ (f * (a + k)) :=
  calc 2 ^ (f * a) * r < 2 ^ (f * a) * (2 ^ f) ^ k :=
        Nat.mul_lt_mul_of_pos_left hr (by positivity)
    _ = 2 ^ (f * (a + k)) := by ring

theorem sub_one_lt_pow (Q i : ℕ) (hQ : 1 ≤ Q) : Q ^ i - 1 < Q ^ i :=
  Nat.sub_lt (Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))) one_pos

theorem pow_add_one_lt (Q i : ℕ) (hQ : 2 ≤ Q) (hi : 1 ≤ i) : Q ^ i + 1 < Q ^ (i + 1) := by
  have h1 : 2 ≤ Q ^ i := hQ.trans (Nat.le_self_pow (by omega) Q)
  rw [pow_succ]
  nlinarith

theorem ordBC_two_eq {f : ℕ} (hf : 1 ≤ f) :
    ordBC 2 (2 ^ f) = 2 ^ (f * 4) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
  rw [ordBC, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf), Nat.div_one, pow_mul 2 f 4]
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)]

theorem notOdd_psp4_two {f : ℕ} (hf : 1 ≤ f) (h : StatedClassicalModel X .PSp 2 2 f) :
    ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordBC 2 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  rw [ordBC_two_eq hf] at hN
  have h2 := odd_pow_sub_one hf (a := 2) (by norm_num)
  have h4 := odd_pow_sub_one hf (a := 4) (by norm_num)
  have hQ : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  refine notOddOrder_of_two_part (g := 1) odd_one (h2.mul h4) (a := f * 4) (b := f * 10)
    (by rw [mul_one, hN]) ?_ (by omega)
  have := two_pow_mul_lt (f := f) (a := 4) (k := 6) (r := ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) (by
    calc ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) < (2 ^ f) ^ 2 * (2 ^ f) ^ 4 :=
          Nat.mul_lt_mul'' (sub_one_lt_pow _ _ hQ) (sub_one_lt_pow _ _ hQ)
      _ = (2 ^ f) ^ 6 := by ring)
  simpa using this

end CharTwo

section Small

theorem cubeFree_of_bounded {N B : ℕ} (hN0 : 0 < N) (hN : N < (B + 1) ^ 3)
    (h : ∀ r < B + 1, 5 ≤ r → r.Prime → ¬ r ^ 3 ∣ N) :
    ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ^ 3 ∣ N := by
  intro r hr hr5 hd
  by_cases hrB : r < B + 1
  · exact h r hrB hr5 hr hd
  · have h1 : (B + 1) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : r ^ 3 ≤ N := Nat.le_of_dvd hN0 hd
    omega

theorem notOdd_psl2_two {f : ℕ} (hf : 1 ≤ f) (h : IsPSL 2 2 f X) : ¬ IsOddOrder (Nat.card X) := by
  obtain ⟨-, -, -, hN⟩ := psl2Data h
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf))
  rw [hg, mul_one] at hN
  refine not_isOddOrder_of_prod (c := 1) (m := 2 ^ f) one_pos (by norm_num) ?_ (by rw [mul_one, hN])
  intro p e hp hp2 he hd
  have h1 : p ∣ 2 ^ f :=
    (dvd_pow_self p (by omega)).trans ((dvd_pow_self (p ^ e) (by norm_num)).trans hd)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))

theorem notOdd_psl2_prime {p' : ℕ} (h : IsPSL 2 p' 1 X) : ¬ IsOddOrder (Nat.card X) := by
  have hp2 : p' ≠ 2 := by
    obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := h
    intro h2
    exact h22 (by simp [h2])
  obtain ⟨-, hp', -, hN⟩ := psl2Data h
  have hodd : Odd p' := hp'.odd_of_ne_two hp2
  have hg : Nat.gcd 2 (p' ^ 1 - 1) = 2 := by
    apply Nat.gcd_eq_left
    rw [pow_one]
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
  rw [hg, pow_one] at hN
  refine not_isOddOrder_of_prod (c := 2) (m := p') (by norm_num) le_rfl ?_ hN
  intro p e hp hp2' he hd
  rcases (Nat.dvd_prime hp').1 hd with h1 | h1
  · have h2 : 1 < (p ^ e) ^ 3 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) hp.one_lt)
    omega
  · rw [← pow_mul] at h1
    exact Nat.Prime.not_prime_pow (by omega : 2 ≤ e * 3) (h1 ▸ hp')

theorem notOdd_u33 (h : IsPSU 3 3 1 X) : ¬ IsOddOrder (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := psu3Data h
  have hN' : Nat.card X = 6048 := by simpa using hN
  rw [hN']
  exact notOddOrder_of_two_part (g := 1) odd_one (by decide : Odd 189) (a := 5) (b := 13)
    (by norm_num) (by norm_num) (by norm_num)

theorem notOdd_l4 (h : StatedClassicalModel X .PSL 4 2 1) : ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordA (4 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have h20160 : ordA (4 - 1) (2 ^ 1) = 20160 := by decide
  rw [hN, h20160]
  exact notOddOrder_of_two_part (g := 1) odd_one (by decide : Odd 315) (a := 6) (b := 15)
    (by norm_num) (by norm_num) (by norm_num)

theorem notOdd_l5 (h : StatedClassicalModel X .PSL 5 2 1) : ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordA (5 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have h9999360 : ordA (5 - 1) (2 ^ 1) = 9999360 := by decide
  rw [hN, h9999360]
  exact notOddOrder_of_two_part (g := 1) odd_one (by decide : Odd 9765) (a := 10) (b := 24)
    (by norm_num) (by norm_num) (by norm_num)

theorem notOdd_l33 (h : IsPSL 3 3 1 X) : ¬ IsOddOrder (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := psl3Data h
  have hN' : Nat.card X = 5616 := by simpa using hN
  rw [hN']
  exact not_isOddOrder_of_cubeFree (cubeFree_of_bounded (B := 17) (by norm_num) (by norm_num)
    (by decide))

theorem notOdd_alt6 (e : X ≃* alternatingGroup (Fin 6)) : ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hN]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_bounded (B := 7) (by norm_num) (by norm_num)
    (by decide))

theorem notOdd_alt7 (e : X ≃* alternatingGroup (Fin 7)) : ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hN]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_bounded (B := 13) (by norm_num) (by norm_num)
    (by decide))

end Small

end CFSG.Quasithin.R3c6
