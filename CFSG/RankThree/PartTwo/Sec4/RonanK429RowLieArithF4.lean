module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

private theorem f4Arith_two_pow_eq {a b X Y : ℕ} (hX : Odd X) (hY : Odd Y)
    (h : 2 ^ a * X = 2 ^ b * Y) : a = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX0 : X ≠ 0 := by obtain ⟨k, hk⟩ := hX; omega
  have hY0 : Y ≠ 0 := by obtain ⟨k, hk⟩ := hY; omega
  have hX2 : ¬ 2 ∣ X := by obtain ⟨k, hk⟩ := hX; omega
  have hY2 : ¬ 2 ∣ Y := by obtain ⟨k, hk⟩ := hY; omega
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (pow_ne_zero a (by norm_num : (2 : ℕ) ≠ 0)) hX0,
    padicValNat.mul (pow_ne_zero b (by norm_num : (2 : ℕ) ≠ 0)) hY0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hX2,
    padicValNat.eq_zero_of_not_dvd hY2] at h1
  omega

private theorem f4Arith_S_odd {f : ℕ} (hf : 1 ≤ f) :
    Odd (3 * (((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) * (2 ^ f - 1))) := by
  have hE : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hE3 : 2 ∣ (2 ^ f) ^ 3 := dvd_pow hE (by norm_num)
  have hE4 : 2 ∣ (2 ^ f) ^ 4 := dvd_pow hE (by norm_num)
  have hE6 : 2 ∣ (2 ^ f) ^ 6 := dvd_pow hE (by norm_num)
  have hpos : 0 < 2 ^ f := by positivity
  have hpos3 : 0 < (2 ^ f) ^ 3 := by positivity
  have hpos4 : 0 < (2 ^ f) ^ 4 := by positivity
  have o6 : Odd ((2 ^ f) ^ 6 + 1) := Nat.odd_iff.mpr (by omega)
  have o4 : Odd ((2 ^ f) ^ 4 - 1) := Nat.odd_iff.mpr (by omega)
  have o3 : Odd ((2 ^ f) ^ 3 + 1) := Nat.odd_iff.mpr (by omega)
  have o1 : Odd (2 ^ f - 1) := Nat.odd_iff.mpr (by omega)
  exact Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr (by norm_num),
    Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨o6, o4⟩, o3⟩, o1⟩⟩

private theorem f4Arith_V_odd {e : ℕ} (he : 1 ≤ e) :
    Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) ∧
      Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := by
  have hE : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have hE2 : 2 ∣ (2 ^ e) ^ 2 := dvd_pow hE (by norm_num)
  have hE3 : 2 ∣ (2 ^ e) ^ 3 := dvd_pow hE (by norm_num)
  have hpos2 : 0 < (2 ^ e) ^ 2 := by positivity
  have hpos3 : 0 < (2 ^ e) ^ 3 := by positivity
  have o2 : Odd ((2 ^ e) ^ 2 - 1) := Nat.odd_iff.mpr (by omega)
  have o3 : Odd ((2 ^ e) ^ 3 - 1) := Nat.odd_iff.mpr (by omega)
  have o3' : Odd ((2 ^ e) ^ 3 + 1) := Nat.odd_iff.mpr (by omega)
  exact ⟨Nat.odd_mul.mpr ⟨o2, o3⟩, Nat.odd_mul.mpr ⟨o2, o3'⟩⟩

private theorem f4Arith_exp {f e V : ℕ} (hf : 1 ≤ f) (hV : Odd V)
    (h : (2 ^ f) ^ 12 * ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) *
        (2 ^ f - 1) * 3 = (2 ^ e) ^ 3 * V) : e = 4 * f := by
  have key : 2 ^ (12 * f) * (3 * (((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) *
      (2 ^ f - 1))) = 2 ^ (3 * e) * V := by
    rw [show (2 : ℕ) ^ (12 * f) = (2 ^ f) ^ 12 by ring,
      show (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 by ring, ← h]
    ring
  have h12 : 12 * f = 3 * e := f4Arith_two_pow_eq (f4Arith_S_odd hf) hV key
  omega

private theorem f4Arith_S_le {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) ≤ 4 * x ^ 14 := by
  have h6 : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have a1 : x ^ 6 + 1 ≤ 2 * x ^ 6 := by omega
  have a2 : x ^ 4 - 1 ≤ x ^ 4 := Nat.sub_le _ _
  have a3 : x ^ 3 + 1 ≤ 2 * x ^ 3 := by omega
  have a4 : x - 1 ≤ x := Nat.sub_le _ _
  calc (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1)
      ≤ (2 * x ^ 6) * x ^ 4 * (2 * x ^ 3) * x :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3) a4
    _ = 4 * x ^ 14 := by ring

private theorem f4Arith_cube_gt {x : ℕ} (hx : 2 ≤ x) : 4 * x ^ 14 < (x ^ 6 - 1) ^ 3 := by
  have h6 : 64 ≤ x ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
  have h4 : 16 ≤ x ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
  obtain ⟨w, hw⟩ : ∃ w, x ^ 6 = w + 1 := ⟨x ^ 6 - 1, by omega⟩
  have hw' : x ^ 6 - 1 = w := by omega
  rw [hw']
  have hw63 : 63 ≤ w := by omega
  have hw2 : 63 * w ^ 2 ≤ w ^ 3 := by
    calc 63 * w ^ 2 ≤ w * w ^ 2 := Nat.mul_le_mul_right _ hw63
      _ = w ^ 3 := by ring
  have hw1 : w ≤ w ^ 2 := by nlinarith
  have hw0 : 1 ≤ w ^ 2 := by nlinarith
  have hcube : (w + 1) ^ 3 < 4 * w ^ 3 := by nlinarith
  have hA : x ^ 14 * 16 ≤ x ^ 14 * x ^ 4 := Nat.mul_le_mul_left _ h4
  have hB : x ^ 14 * x ^ 4 = (w + 1) ^ 3 := by rw [← hw]; ring
  omega

private theorem f4Arith_pure {x T : ℕ} (hx : 2 ≤ x) (hT : x ^ 12 ≤ 2 * T)
    (h : x ^ 12 * (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) * 3 =
      (x ^ 4) ^ 3 * (((x ^ 4) ^ 2 - 1) * T)) : False := by
  have hx0 : 0 < x := by omega
  have hx12 : 0 < x ^ 12 := pow_pos hx0 12
  have hx14 : 0 < x ^ 14 := pow_pos hx0 14
  have e1 : (x ^ 4) ^ 3 = x ^ 12 := by ring
  have e2 : (x ^ 4) ^ 2 = x ^ 8 := by ring
  rw [e1, e2] at h
  have h3 : 3 * ((x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1)) = (x ^ 8 - 1) * T := by
    apply Nat.eq_of_mul_eq_mul_left hx12
    calc x ^ 12 * (3 * ((x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1)))
        = x ^ 12 * (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) * 3 := by ring
      _ = x ^ 12 * ((x ^ 8 - 1) * T) := h
  have hS := f4Arith_S_le hx
  have h8 : 256 ≤ x ^ 8 := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ x ^ 8 := Nat.pow_le_pow_left hx 8
  have h6 : 64 ≤ x ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
  have hA : x ^ 8 ≤ 2 * (x ^ 8 - 1) := by omega
  have hprod : x ^ 8 * x ^ 12 ≤ (2 * (x ^ 8 - 1)) * (2 * T) := Nat.mul_le_mul hA hT
  have hfin : x ^ 8 * x ^ 12 ≤ 4 * ((x ^ 8 - 1) * T) := by
    calc x ^ 8 * x ^ 12 ≤ (2 * (x ^ 8 - 1)) * (2 * T) := hprod
      _ = 4 * ((x ^ 8 - 1) * T) := by ring
  have hlow : 64 * x ^ 14 ≤ x ^ 8 * x ^ 12 := by
    calc 64 * x ^ 14 ≤ x ^ 6 * x ^ 14 := Nat.mul_le_mul_right _ h6
      _ = x ^ 8 * x ^ 12 := by ring
  omega

private theorem f4Arith_odd {f r T : ℕ} (hf : 1 ≤ f) (hr : Odd r) (hr3 : ¬ 3 ∣ r)
    (hr5 : 5 ≤ r) (hT : T = r ^ 3 - 1 ∨ T = r ^ 3 + 1)
    (h : (2 ^ f) ^ 12 * ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) *
        (2 ^ f - 1) * 3 = r ^ 3 * ((r ^ 2 - 1) * T)) : False := by
  have hx2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hx4 : 16 ≤ (2 ^ f) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hx2 4)
  obtain ⟨S, hS⟩ : ∃ S, S = ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) *
      (2 ^ f - 1) := ⟨_, rfl⟩
  have h' : (2 ^ f) ^ 12 * S * 3 = r ^ 3 * ((r ^ 2 - 1) * T) := by
    rw [hS, ← h]
    ring
  have hpow : (2 : ℕ) ^ (12 * f) = (2 ^ f) ^ 12 := by ring
  have hcop : r ^ 3 ∣ 3 * (2 ^ (12 * f) * S) :=
    ⟨(r ^ 2 - 1) * T, by rw [hpow, ← h']; ring⟩
  have hdvdT : 2 ^ (12 * f) ∣ r ^ 3 * (r ^ 2 - 1) * T :=
    ⟨3 * S, by rw [hpow, mul_assoc, ← h']; ring⟩
  have hdvd : 2 ^ (12 * f) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) ∨
      2 ^ (12 * f) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
    rcases hT with rfl | rfl
    · exact Or.inl hdvdT
    · exact Or.inr hdvdT
  have hle := CFSG.RankThree.PartTwo.Sec19.Step1917Steps.two_pow_le_of_dvd_sl3Order hr
    (by omega) (by omega) hdvd
  rw [show 12 * f / 2 = 6 * f by omega, show (2 : ℕ) ^ (6 * f) = (2 ^ f) ^ 6 by ring] at hle
  have hcube : r ^ 3 ∣ S :=
    CFSG.RankThree.PartTwo.Sec19.Step1917Steps.pow_three_dvd_of_coprime (N := 12 * f) hr hr3 hcop
  have hSpos : 0 < S := by
    rw [hS]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by positivity))
      (by omega)
  have hSle : S ≤ 4 * (2 ^ f) ^ 14 := by
    rw [hS]
    exact f4Arith_S_le hx2
  have hrS : r ^ 3 ≤ S := Nat.le_of_dvd hSpos hcube
  have hcg : 4 * (2 ^ f) ^ 14 < ((2 ^ f) ^ 6 - 1) ^ 3 := f4Arith_cube_gt hx2
  have hsub : (2 ^ f) ^ 6 - 1 ≤ r := by omega
  have hpow3 : ((2 ^ f) ^ 6 - 1) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hsub 3
  exact absurd (((hrS.trans hSle).trans_lt hcg).trans_le hpow3) (lt_irrefl _)

theorem f4_mul_three_ne_L3 {f p e : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    CFSG.Open.ordTwistedF4 (2 ^ f) * 3 ≠ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
  intro h
  unfold CFSG.Open.ordTwistedF4 at h
  have hx2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  by_cases hp2 : p = 2
  · subst hp2
    have he4 : e = 4 * f := f4Arith_exp hf (f4Arith_V_odd he).1 h
    subst he4
    rw [show (2 : ℕ) ^ (4 * f) = (2 ^ f) ^ 4 by ring] at h
    have hA : 2 ≤ (2 ^ f) ^ 12 := le_trans (by norm_num) (Nat.pow_le_pow_left hx2 12)
    have hB : ((2 ^ f) ^ 4) ^ 3 = (2 ^ f) ^ 12 := by ring
    exact f4Arith_pure hx2 (by rw [hB]; omega) h
  · have hodd_p : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    have hr5 : 5 ≤ p ^ e := le_trans hp5 (Nat.le_self_pow (by omega) p)
    have hr_odd : Odd (p ^ e) := Odd.pow (Nat.odd_iff.mpr hodd_p)
    have hr3 : ¬ 3 ∣ p ^ e := fun h3 =>
      hp3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm)
    exact f4Arith_odd hf hr_odd hr3 hr5 (Or.inl rfl) h

theorem f4_mul_three_ne_U3 {f p e : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    CFSG.Open.ordTwistedF4 (2 ^ f) * 3 ≠ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  intro h
  unfold CFSG.Open.ordTwistedF4 at h
  have hx2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  by_cases hp2 : p = 2
  · subst hp2
    have he4 : e = 4 * f := f4Arith_exp hf (f4Arith_V_odd he).2 h
    subst he4
    rw [show (2 : ℕ) ^ (4 * f) = (2 ^ f) ^ 4 by ring] at h
    have hA : 2 ≤ (2 ^ f) ^ 12 := le_trans (by norm_num) (Nat.pow_le_pow_left hx2 12)
    have hB : ((2 ^ f) ^ 4) ^ 3 = (2 ^ f) ^ 12 := by ring
    exact f4Arith_pure hx2 (by rw [hB]; omega) h
  · have hodd_p : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    have hr5 : 5 ≤ p ^ e := le_trans hp5 (Nat.le_self_pow (by omega) p)
    have hr_odd : Odd (p ^ e) := Odd.pow (Nat.odd_iff.mpr hodd_p)
    have hr3 : ¬ 3 ∣ p ^ e := fun h3 =>
      hp3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm)
    exact f4Arith_odd hf hr_odd hr3 hr5 (Or.inr rfl) h

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
