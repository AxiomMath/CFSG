module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HDefs
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace OrdG2D4

open CFSG.Open (ordG2 ordTrialityD4)

lemma three_dvd_sq_sub_one {a : ℕ} (h3 : ¬ 3 ∣ a) : 3 ∣ a ^ 2 - 1 := by
  have : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h | h
  · have : a ^ 2 % 3 = 1 := by simp [pow_two, Nat.mul_mod, h]
    omega
  · have : a ^ 2 % 3 = 1 := by simp [pow_two, Nat.mul_mod, h]
    omega

lemma v3_pow6_sub_one {a : ℕ} (ha : 2 ≤ a) (h3 : ¬ 3 ∣ a) :
    padicValNat 3 (a ^ 6 - 1) = padicValNat 3 (a ^ 2 - 1) + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : 1 < a ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have h3' : ¬ 3 ∣ a ^ 2 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have := padicValNat.pow_sub_pow (p := 3) (by decide) (x := a ^ 2) (y := 1) hx
    (by simpa using three_dvd_sq_sub_one h3) h3' (n := 3) (by norm_num)
  rw [one_pow] at this
  rw [show a ^ 6 = (a ^ 2) ^ 3 by ring, this]
  simp

lemma v3_quartic {a : ℕ} (ha : 2 ≤ a) (h3 : ¬ 3 ∣ a) :
    padicValNat 3 (a ^ 8 + a ^ 4 + 1) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : 1 < a ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
  have h3' : ¬ 3 ∣ a ^ 4 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have h3'' : ¬ 3 ∣ a ^ 2 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hd : 3 ∣ a ^ 4 - 1 := by
    have := three_dvd_sq_sub_one h3''
    rwa [← pow_mul] at this
  have key := padicValNat.pow_sub_pow (p := 3) (by decide) (x := a ^ 4) (y := 1) hx
    (by simpa using hd) h3' (n := 3) (by norm_num)
  rw [one_pow] at key
  have hfac : (a ^ 4) ^ 3 - 1 = (a ^ 4 - 1) * (a ^ 8 + a ^ 4 + 1) := by
    have hle : 1 ≤ a ^ 4 := hx.le
    zify [hle, show 1 ≤ (a ^ 4) ^ 3 from Nat.one_le_pow _ _ (by omega)]
    ring
  have hne1 : a ^ 4 - 1 ≠ 0 := by omega
  have hne2 : a ^ 8 + a ^ 4 + 1 ≠ 0 := by omega
  rw [hfac, padicValNat.mul hne1 hne2] at key
  simp at key
  omega

lemma three_dvd_cases {b : ℕ} (hb : 3 ∣ b) (hb2 : 2 ≤ b) :
    ¬ 3 ∣ b ^ 6 - 1 ∧ ¬ 3 ∣ b ^ 2 - 1 ∧ ¬ 3 ∣ b ^ 8 + b ^ 4 + 1 := by
  have h0 : b % 3 = 0 := Nat.mod_eq_zero_of_dvd hb
  have h6 : b ^ 6 % 3 = 0 := by simp [Nat.pow_mod, h0]
  have h2 : b ^ 2 % 3 = 0 := by simp [Nat.pow_mod, h0]
  have h8 : b ^ 8 % 3 = 0 := by simp [Nat.pow_mod, h0]
  have h4 : b ^ 4 % 3 = 0 := by simp [Nat.pow_mod, h0]
  have i6 : 1 ≤ b ^ 6 := Nat.one_le_pow _ _ (by omega)
  have i2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_, ?_⟩ <;> omega

lemma v3_ordG2_of_not_dvd {a : ℕ} (ha : 3 ≤ a) (h3 : ¬ 3 ∣ a) :
    padicValNat 3 (ordG2 a) = 2 * padicValNat 3 (a ^ 2 - 1) + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold ordG2
  have h6 : a ^ 6 ≠ 0 := by positivity
  have h6' : a ^ 6 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 6) (by norm_num) (show 1 < a by omega); omega
  have h2' : a ^ 2 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 2) (by norm_num) (show 1 < a by omega); omega
  have h36 : ¬ 3 ∣ a ^ 6 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  rw [padicValNat.mul (mul_ne_zero h6 h6') h2', padicValNat.mul h6 h6',
    padicValNat.eq_zero_of_not_dvd h36, v3_pow6_sub_one (by omega) h3]
  omega

lemma v3_ordTri_of_not_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    padicValNat 3 (ordTrialityD4 b) = 2 * padicValNat 3 (b ^ 2 - 1) + 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold ordTrialityD4
  have h12 : b ^ 12 ≠ 0 := by positivity
  have hq : b ^ 8 + b ^ 4 + 1 ≠ 0 := by positivity
  have h6' : b ^ 6 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 6) (by norm_num) (show 1 < b by omega); omega
  have h2' : b ^ 2 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 2) (by norm_num) (show 1 < b by omega); omega
  have h312 : ¬ 3 ∣ b ^ 12 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero h12 hq) h6') h2',
    padicValNat.mul (mul_ne_zero h12 hq) h6', padicValNat.mul h12 hq,
    padicValNat.eq_zero_of_not_dvd h312, v3_quartic hb h3, v3_pow6_sub_one hb h3]
  omega

lemma v3_ordG2_of_dvd {a : ℕ} (ha : 3 ≤ a) (h3 : 3 ∣ a) :
    padicValNat 3 (ordG2 a) = 6 * padicValNat 3 a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h6, h2, -⟩ := three_dvd_cases h3 (by omega)
  unfold ordG2
  have h6' : a ^ 6 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 6) (by norm_num) (show 1 < a by omega); omega
  have h2' : a ^ 2 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 2) (by norm_num) (show 1 < a by omega); omega
  have h0 : a ^ 6 ≠ 0 := by positivity
  rw [padicValNat.mul (mul_ne_zero h0 h6') h2', padicValNat.mul h0 h6',
    padicValNat.eq_zero_of_not_dvd h6, padicValNat.eq_zero_of_not_dvd h2,
    padicValNat.pow a 6]
  omega

lemma v3_ordTri_of_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) :
    padicValNat 3 (ordTrialityD4 b) = 12 * padicValNat 3 b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h6, h2, h8⟩ := three_dvd_cases h3 hb
  unfold ordTrialityD4
  have h12 : b ^ 12 ≠ 0 := by positivity
  have hq : b ^ 8 + b ^ 4 + 1 ≠ 0 := by positivity
  have h6' : b ^ 6 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 6) (by norm_num) (show 1 < b by omega); omega
  have h2' : b ^ 2 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 2) (by norm_num) (show 1 < b by omega); omega
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero h12 hq) h6') h2',
    padicValNat.mul (mul_ne_zero h12 hq) h6', padicValNat.mul h12 hq,
    padicValNat.eq_zero_of_not_dvd h6, padicValNat.eq_zero_of_not_dvd h2,
    padicValNat.eq_zero_of_not_dvd h8, padicValNat.pow b 12]
  omega

lemma ordG2_lt_pow14 {a : ℕ} (ha : 2 ≤ a) : ordG2 a < a ^ 14 := by
  unfold ordG2
  have h6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h : (a ^ 6 - 1) * (a ^ 2 - 1) < a ^ 6 * a ^ 2 :=
    Nat.mul_lt_mul'' (by omega) (by omega)
  calc a ^ 6 * (a ^ 6 - 1) * (a ^ 2 - 1) = a ^ 6 * ((a ^ 6 - 1) * (a ^ 2 - 1)) := by ring
    _ < a ^ 6 * (a ^ 6 * a ^ 2) := Nat.mul_lt_mul_of_pos_left h (by positivity)
    _ = a ^ 14 := by ring

lemma pow14_le_four_mul_ordTri {b : ℕ} (hb : 2 ≤ b) : (b ^ 2) ^ 14 ≤ 4 * ordTrialityD4 b := by
  unfold ordTrialityD4
  have h6 : 2 ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hb 6
  have h2 : 2 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
  have e1 : b ^ 6 ≤ 2 * (b ^ 6 - 1) := by omega
  have e2 : b ^ 2 ≤ 2 * (b ^ 2 - 1) := by omega
  have e3 : b ^ 8 ≤ b ^ 8 + b ^ 4 + 1 := by omega
  calc (b ^ 2) ^ 14 = b ^ 12 * b ^ 8 * b ^ 6 * b ^ 2 := by ring
    _ ≤ b ^ 12 * (b ^ 8 + b ^ 4 + 1) * (2 * (b ^ 6 - 1)) * (2 * (b ^ 2 - 1)) := by gcongr
    _ = 4 * (b ^ 12 * (b ^ 8 + b ^ 4 + 1) * (b ^ 6 - 1) * (b ^ 2 - 1)) := by ring

lemma ordTri_lt_ordG2_sq {b : ℕ} (hb : 2 ≤ b) : ordTrialityD4 b < ordG2 (b ^ 2) := by
  unfold ordTrialityD4 ordG2
  obtain ⟨s, hs⟩ : ∃ s, s = b ^ 2 := ⟨_, rfl⟩
  have hs4 : 4 ≤ s := by rw [hs]; nlinarith
  have e1 : b ^ 12 = s ^ 6 := by rw [hs]; ring
  have e2 : b ^ 8 = s ^ 4 := by rw [hs]; ring
  have e3 : b ^ 4 = s ^ 2 := by rw [hs]; ring
  have e4 : b ^ 6 = s ^ 3 := by rw [hs]; ring
  rw [e1, e2, e3, e4, ← hs]
  have key : (s ^ 4 + s ^ 2 + 1) * (s ^ 3 - 1) * (s - 1) < (s ^ 6 - 1) * (s ^ 2 - 1) := by
    have h1 : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h4 : (s : ℤ) ^ 3 - 1 > 0 := by
      have : (4 : ℤ) ^ 3 ≤ (s : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hs4) 3
      linarith
    have h5 : (s : ℤ) - 1 > 0 := by
      have : (4 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs4
      linarith
    have h6 : (s : ℤ) ^ 3 - (s : ℤ) ^ 2 + s > 0 := by
      have : (4 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs4
      nlinarith [sq_nonneg ((s : ℤ) - 1), mul_pos h5 h5]
    have hid : ((s : ℤ) ^ 6 - 1) * ((s : ℤ) ^ 2 - 1) -
        ((s : ℤ) ^ 4 + (s : ℤ) ^ 2 + 1) * ((s : ℤ) ^ 3 - 1) * ((s : ℤ) - 1) =
        ((s : ℤ) ^ 3 - 1) * ((s : ℤ) - 1) * ((s : ℤ) ^ 3 - (s : ℤ) ^ 2 + s) := by ring
    have hpos := mul_pos (mul_pos h4 h5) h6
    zify [h1, h2, h3, (by omega : 1 ≤ s)]
    linarith
  have hs6 : 0 < s ^ 6 := by positivity
  calc s ^ 6 * (s ^ 4 + s ^ 2 + 1) * (s ^ 3 - 1) * (s - 1)
      = s ^ 6 * ((s ^ 4 + s ^ 2 + 1) * (s ^ 3 - 1) * (s - 1)) := by ring
    _ < s ^ 6 * ((s ^ 6 - 1) * (s ^ 2 - 1)) := Nat.mul_lt_mul_of_pos_left key hs6
    _ = s ^ 6 * (s ^ 6 - 1) * (s ^ 2 - 1) := by ring

theorem ordG2_ne_ordTrialityD4 (q q' : TauCeti.PrimePower) (hq : 3 ≤ q.card) :
    ordG2 q.card ≠ ordTrialityD4 q'.card := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb : 2 ≤ q'.card := by
    rw [TauCeti.PrimePower.card_def]
    exact q'.prime_p.two_le.trans (Nat.le_self_pow q'.exponent_pos.ne' _)
  have hcard : ∀ r : TauCeti.PrimePower, 3 ∣ r.card → r.card = 3 ^ r.exponent := by
    intro r hr
    rw [TauCeti.PrimePower.card_def] at hr ⊢
    have h1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three r.prime_p).mp
      (Nat.prime_three.dvd_of_dvd_pow hr)
    rw [← h1]
  have hv := congrArg (padicValNat 3) h
  by_cases h3a : 3 ∣ q.card <;> by_cases h3b : 3 ∣ q'.card
  · have ha := hcard q h3a
    have hb' := hcard q' h3b
    rw [v3_ordG2_of_dvd hq h3a, v3_ordTri_of_dvd hb h3b, ha, hb', padicValNat.prime_pow,
      padicValNat.prime_pow] at hv
    have he : q.exponent = 2 * q'.exponent := by omega
    have hq2 : q.card = q'.card ^ 2 := by rw [ha, hb', ← pow_mul, he, mul_comm]
    rw [hq2] at h
    exact (ordTri_lt_ordG2_sq hb).ne' h
  · have ha := hcard q h3a
    rw [v3_ordG2_of_dvd hq h3a, v3_ordTri_of_not_dvd hb h3b, ha, padicValNat.prime_pow] at hv
    have hu : 2 ≤ q'.card ^ 2 := by nlinarith
    have hpos : 0 < q'.card ^ 2 - 1 := by omega
    have hle : 3 ^ padicValNat 3 (q'.card ^ 2 - 1) ≤ q'.card ^ 2 - 1 :=
      Nat.le_of_dvd hpos pow_padicValNat_dvd
    have he : 1 ≤ q.exponent := q.exponent_pos
    have h3a' : 3 * q.card < q'.card ^ 2 := by
      have h1 : 3 ^ (q.exponent + 1) ≤ 3 ^ padicValNat 3 (q'.card ^ 2 - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 3 * q.card = 3 ^ (q.exponent + 1) := by rw [ha]; ring
      omega
    have h1 := ordG2_lt_pow14 (show 2 ≤ q.card by omega)
    have h2 := pow14_le_four_mul_ordTri hb
    have h4 : (3 * q.card) ^ 14 < (q'.card ^ 2) ^ 14 := Nat.pow_lt_pow_left h3a' (by norm_num)
    have h5 : 3 ^ 14 * q.card ^ 14 < 4 * q.card ^ 14 := by
      calc 3 ^ 14 * q.card ^ 14 = (3 * q.card) ^ 14 := (mul_pow _ _ _).symm
        _ < (q'.card ^ 2) ^ 14 := h4
        _ ≤ 4 * ordTrialityD4 q'.card := h2
        _ = 4 * ordG2 q.card := by rw [h]
        _ < 4 * q.card ^ 14 := by omega
    have h6 := Nat.lt_of_mul_lt_mul_right h5
    norm_num at h6
  · rw [v3_ordG2_of_not_dvd hq h3a, v3_ordTri_of_dvd hb h3b] at hv
    omega
  · rw [v3_ordG2_of_not_dvd hq h3a, v3_ordTri_of_not_dvd hb h3b] at hv
    omega

end OrdG2D4

namespace Psl2Orders

def f (x : ℕ) : ℕ := x * (x ^ 2 - 1)

lemma f_strictMono {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : f a < f b := by
  unfold f
  have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  exact Nat.mul_lt_mul'' hab (by omega)

lemma eq_of_f_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : f a = f b) : a = b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact absurd h (f_strictMono ha h1).ne
  · exact h1
  · exact absurd h (f_strictMono hb h1).ne'

lemma f_two_mul_sub_one {a : ℕ} (ha : 4 ≤ a) : 2 * f a < f (2 * a - 1) := by
  unfold f
  obtain ⟨t, rfl⟩ : ∃ t, a = t + 4 := ⟨a - 4, by omega⟩
  have e1 : 2 * (t + 4) - 1 = 2 * t + 7 := by omega
  rw [e1]
  have h1 : 1 ≤ (t + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (2 * t + 7) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  nlinarith [sq_nonneg (t : ℤ), mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg t)]

lemma f_mono {c b : ℕ} (hc : 1 ≤ c) (hcb : c ≤ b) : f c ≤ f b := by
  rcases hcb.eq_or_lt with h | h
  · rw [h]
  · exact (f_strictMono hc h).le

lemma cases_eq {a b : ℕ} (ha : 4 ≤ a) (hb : 5 ≤ b) (h : f b = 2 * f a)
    (hd : a ∣ b - 1 ∨ a ∣ b + 1) : a = 4 ∧ b = 5 := by
  have hlt : b < 2 * a - 1 := by
    by_contra hcon
    push Not at hcon
    have := f_mono (show 1 ≤ 2 * a - 1 by omega) hcon
    have h2 := f_two_mul_sub_one ha
    omega
  have hab : b = a + 1 ∨ b = a - 1 := by
    rcases hd with ⟨t, ht⟩ | ⟨t, ht⟩
    · rcases t with _ | _ | t
      · omega
      · left; omega
      · exfalso
        have h2 : 2 * a ≤ a * (t + 1 + 1) := by nlinarith [Nat.zero_le (a * t)]
        omega
    · rcases t with _ | _ | t
      · omega
      · right; omega
      · exfalso
        have h2 : 2 * a ≤ a * (t + 1 + 1) := by nlinarith [Nat.zero_le (a * t)]
        omega
  rcases hab with rfl | rfl
  · unfold f at h
    have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2] at h
    have : (a : ℤ) * (a - 4) * (a + 1) = 0 := by nlinarith
    have ha' : (a : ℤ) ≠ 0 := by omega
    have ha'' : (a : ℤ) + 1 ≠ 0 := by omega
    have : (a : ℤ) - 4 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h ha'
        · exact h
      · exact absurd h ha''
    omega
  · exfalso
    unfold f at h
    have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (a - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h h2 hb
    zify [h1, h2] at h
    nlinarith

lemma even_odd_case {k b : ℕ} (hk : 2 ≤ k) (hb : 5 ≤ b) (hbo : Odd b)
    (h : f b = 2 * f (2 ^ k)) : 2 ^ k = 4 ∧ b = 5 := by
  have ha4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hcop : Nat.Coprime (2 ^ (k + 1)) b :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hbo)
  have hdvd : 2 ^ (k + 1) ∣ b * (b ^ 2 - 1) := by
    unfold f at h
    rw [h]
    exact ⟨2 ^ (2 * k) - 1, by rw [pow_succ, ← pow_mul]; ring⟩
  have hdvd' : 2 ^ (k + 1) ∣ b ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨m, hm⟩ := hbo
  have hb2 : b ^ 2 - 1 = 4 * (m * (m + 1)) := by
    subst hm
    have : 1 ≤ (2 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this]
    ring
  rw [hb2] at hdvd'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hdvd'' : 2 ^ j ∣ m * (m + 1) := by
    have : 2 ^ (j + 1 + 1) = 4 * 2 ^ j := by rw [pow_succ, pow_succ]; ring
    rw [this] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd'
  have hj : 2 ^ j ∣ m ∨ 2 ^ j ∣ m + 1 := by
    by_cases hm2 : 2 ∣ m
    · left
      have hc : Nat.Coprime (2 ^ j) (m + 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_two_left]
        obtain ⟨u, hu⟩ := hm2
        exact ⟨u, by omega⟩
      exact hc.dvd_of_dvd_mul_right hdvd''
    · right
      have hc : Nat.Coprime (2 ^ j) m := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_two_left]
        exact Nat.odd_iff.mpr (by omega)
      exact hc.dvd_of_dvd_mul_left hdvd''
  have hd : 2 ^ (j + 1) ∣ b - 1 ∨ 2 ^ (j + 1) ∣ b + 1 := by
    rcases hj with ⟨t, ht⟩ | ⟨t, ht⟩
    · left
      refine ⟨t, ?_⟩
      have h1 : b - 1 = 2 * m := by omega
      rw [h1, ht]
      ring
    · right
      refine ⟨t, ?_⟩
      have h1 : b + 1 = 2 * (m + 1) := by omega
      rw [h1, ht]
      ring
  exact cases_eq ha4 hb h hd

lemma gcd_two_sub_one_of_even {a : ℕ} (ha : Even a) (h1 : 1 ≤ a) : Nat.gcd 2 (a - 1) = 1 := by
  obtain ⟨u, hu⟩ := ha
  have : a - 1 = 2 * (u - 1) + 1 := by omega
  rw [this]
  simp

lemma gcd_two_sub_one_of_odd {a : ℕ} (ha : Odd a) : Nat.gcd 2 (a - 1) = 2 := by
  obtain ⟨u, hu⟩ := ha
  have : a - 1 = 2 * u := by omega
  rw [this]
  simp

theorem psl_orders_eq {a b N : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b)
    (ha' : (∃ k, a = 2 ^ k) ∨ Odd a) (hb' : (∃ k, b = 2 ^ k) ∨ Odd b)
    (hNa : N * Nat.gcd 2 (a - 1) = f a) (hNb : N * Nat.gcd 2 (b - 1) = f b) :
    a = b ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) := by
  have hpow : ∀ {c k : ℕ}, 4 ≤ c → c = 2 ^ k → 2 ≤ k ∧ Even c := by
    intro c k hc hck
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      interval_cases k <;> simp at hck <;> omega
    · rw [hck]
      exact (Nat.even_pow.mpr ⟨even_two, by rintro rfl; simp at hck; omega⟩)
  rcases ha' with ⟨k, hk⟩ | hao <;> rcases hb' with ⟨l, hl⟩ | hbo
  · obtain ⟨hk2, hke⟩ := hpow ha hk
    obtain ⟨hl2, hle⟩ := hpow hb hl
    rw [gcd_two_sub_one_of_even hke (by omega)] at hNa
    rw [gcd_two_sub_one_of_even hle (by omega)] at hNb
    left
    exact eq_of_f_eq (by omega) (by omega) (by omega)
  · obtain ⟨hk2, hke⟩ := hpow ha hk
    rw [gcd_two_sub_one_of_even hke (by omega)] at hNa
    rw [gcd_two_sub_one_of_odd hbo] at hNb
    right; left
    have hb5 : 5 ≤ b := by
      obtain ⟨u, hu⟩ := hbo
      omega
    subst hk
    have := even_odd_case hk2 hb5 hbo (by omega)
    exact ⟨this.1, this.2⟩
  · obtain ⟨hl2, hle⟩ := hpow hb hl
    rw [gcd_two_sub_one_of_odd hao] at hNa
    rw [gcd_two_sub_one_of_even hle (by omega)] at hNb
    right; right
    have ha5 : 5 ≤ a := by
      obtain ⟨u, hu⟩ := hao
      omega
    subst hl
    have := even_odd_case hl2 ha5 hao (by omega)
    exact ⟨this.2, this.1⟩
  · rw [gcd_two_sub_one_of_odd hao] at hNa
    rw [gcd_two_sub_one_of_odd hbo] at hNb
    left
    exact eq_of_f_eq (by omega) (by omega) (by omega)

end Psl2Orders

section Psl2

open CFSG.Assembly.RankThreeEven (projSL)

theorem psl2IsoOrders_holds :
    ∀ (p n p' n' : ℕ) [Fact p.Prime] [Fact p'.Prime], 4 ≤ p ^ n → 4 ≤ p' ^ n' →
      Nonempty (projSL 2 (GaloisField p n) ≃* projSL 2 (GaloisField p' n')) →
        p ^ n = p' ^ n' ∨ (p ^ n = 4 ∧ p' ^ n' = 5) ∨ (p ^ n = 5 ∧ p' ^ n' = 4) := by
  intro p n p' n' _ _ hs hs' ⟨e⟩
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hs
  have hn' : n' ≠ 0 := by
    rintro rfl
    simp at hs'
  have h1 := Sec11.KSListsProof.card_projSL_two_mul (GaloisField p n)
  have h2 := Sec11.KSListsProof.card_projSL_two_mul (GaloisField p' n')
  rw [GaloisField.card p n hn] at h1
  rw [GaloisField.card p' n' hn'] at h2
  have hN : Nat.card (projSL 2 (GaloisField p n)) = Nat.card (projSL 2 (GaloisField p' n')) :=
    Nat.card_congr e.toEquiv
  rw [← hN] at h2
  have hpow : ∀ (q m : ℕ) [hq : Fact q.Prime], (∃ k, q ^ m = 2 ^ k) ∨ Odd (q ^ m) := by
    intro q m hq
    rcases hq.out.eq_two_or_odd' with rfl | hodd
    · exact Or.inl ⟨m, rfl⟩
    · exact Or.inr (hodd.pow)
  exact Psl2Orders.psl_orders_eq hs hs' (hpow p n) (hpow p' n') h1 h2

end Psl2

section Groups


theorem kfNonIsoG2D4_holds : KFNonIsoG2D4 := by
  intro q q' hq hq'
  refine ⟨fun e => ?_⟩
  have h3 : 3 ≤ q.card := by
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
    rwa [TauCeti.LieTypeIndex.inStandardRange_iff] at h1
  have h1 := Sec11.KSListsProof.card_G2_carrier q hq
  have h2 := Sec11.KSListsProof.card_trialityD4_carrier q' hq'
  have h := Nat.card_congr e.toEquiv
  rw [h1, h2] at h
  exact OrdG2D4.ordG2_ne_ordTrialityD4 q q' h3 h

end Groups

end CFSG.RankThree.PartTwo.Sec12
