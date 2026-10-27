module

public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F6CatRecogZ4wrZ2
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.F134

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem sq_sub_one_eq (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : 1 ≤ q := hq
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [h1, h2]
    ring

theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  rw [sq_sub_one_eq]
  have : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _

theorem three_dvd_sq_sub_one {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 :=
  ((Nat.Prime.dvd_mul Nat.prime_three).1 (three_dvd_mul_sq_sub_one q)).resolve_left hq

theorem not_three_dvd_two_pow (n : ℕ) : ¬ 3 ∣ 2 ^ n := fun h => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem dvd_div_of_dvd_of_coprime {a d N : ℕ} (hd : d ∣ N) (ha : a ∣ N) (hcop : Nat.Coprime a d) :
    a ∣ N / d := by
  obtain ⟨m, rfl⟩ := hd
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp
  · rw [Nat.mul_div_cancel_left m hpos]
    exact hcop.dvd_of_dvd_mul_left ha

theorem three_dvd_div_three {N : ℕ} (h : 9 ∣ N) : 3 ∣ N / 3 := by
  obtain ⟨m, rfl⟩ := h
  rw [show 9 * m = 3 * (3 * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact Dvd.intro m rfl

theorem three_dvd_div_gcd {N x : ℕ} (h1 : ¬ 3 ∣ x → 3 ∣ N) (h3 : 3 ∣ x → 9 ∣ N) :
    3 ∣ N / Nat.gcd 3 x := by
  by_cases hx : 3 ∣ x
  · rw [Nat.gcd_eq_left hx]
    exact three_dvd_div_three (h3 hx)
  · have hcop : Nat.gcd 3 x = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hx
    rw [hcop, Nat.div_one]
    exact h1 hx

theorem three_dvd_card_statedProj_statedSL_two {K : Type} [Field K] [Finite K] :
    3 ∣ Nat.card (StatedProj (StatedSL 2 K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2),
    show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton,
    show 2 * (2 - 1) / 2 = 1 from rfl, pow_one]
  set q := Nat.card K
  refine dvd_div_of_dvd_of_coprime ?_ (three_dvd_mul_sq_sub_one q) ?_
  · refine (Nat.gcd_dvd_right 2 (q - 1)).trans (Dvd.dvd.mul_left ?_ q)
    rw [sq_sub_one_eq]
    exact Dvd.intro _ rfl
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num)

theorem three_dvd_card_statedProj_statedSL_three {K : Type} [Field K] [Finite K] :
    3 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  rw [CFSG.Quasithin.F6.card_statedProj_sl_three]
  set q := Nat.card K
  refine three_dvd_div_gcd (fun _ => ?_) (fun h3 => ?_)
  · exact (three_dvd_mul_sq_sub_one q).trans
      (mul_dvd_mul (dvd_pow_self q (by norm_num)) (dvd_mul_right _ _))
  · have h9 : 9 ∣ (q - 1) * (q - 1) := by
      rw [show 9 = 3 * 3 by rfl]
      exact mul_dvd_mul h3 h3
    refine h9.trans (Dvd.dvd.mul_left (mul_dvd_mul ?_ ?_) _)
    · simpa using Nat.sub_one_dvd_pow_sub_one q 2
    · simpa using Nat.sub_one_dvd_pow_sub_one q 3

theorem three_dvd_card_statedProj_statedSU_three {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) :
    3 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) := by
  rw [CFSG.Quasithin.F6.card_statedProj_su_three hp hf hK]
  set q := p ^ f
  refine three_dvd_div_gcd (fun _ => ?_) (fun h3 => ?_)
  · exact (three_dvd_mul_sq_sub_one q).trans
      (mul_dvd_mul (dvd_pow_self q (by norm_num)) (dvd_mul_right _ _))
  · have h9 : 9 ∣ (q + 1) * (q + 1) := by
      rw [show 9 = 3 * 3 by rfl]
      exact mul_dvd_mul h3 h3
    refine h9.trans (Dvd.dvd.mul_left (mul_dvd_mul ?_ ?_) _)
    · rw [sq_sub_one_eq]
      exact Dvd.intro_left _ rfl
    · simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)

theorem charP_two_of_card_eq {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem three_dvd_card_of_statedPSp_two_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSp 2 2 n) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have := charP_two_of_card_eq hK
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), hK]
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
  simpa using three_dvd_sq_sub_one (not_three_dvd_two_pow n)

theorem three_dvd_card_of_statedPSL_two {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSL 2 p f) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_statedProj_statedSL_two

theorem three_dvd_card_of_statedPSL_three {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSL 3 p f) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_statedProj_statedSL_three

theorem three_dvd_card_of_statedPSU_three {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSU 3 p f) : 3 ∣ Nat.card X := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_statedProj_statedSU_three hp hf hK

theorem three_dvd_card_of_statedPSL_four_five {X : Type} [Group X] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : StatedClassicalModel X .PSL n 2 1) : 3 ∣ Nat.card X := by
  rcases hn with rfl | rfl
  · rw [CFSG.Quasithin.F420.card_of_l42 h]
    norm_num
  · rw [CFSG.Quasithin.F420.card_of_l52 h]
    norm_num

theorem three_dvd_card_of_g2_two
    {X : Type} [Group X] {n : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 n) : 3 ∣ Nat.card X := by
  rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h]
  show 3 ∣ CFSG.Open.ordG2 (2 ^ n)
  rw [CFSG.Open.ordG2]
  exact Dvd.dvd.mul_left (three_dvd_sq_sub_one (not_three_dvd_two_pow n)) _

theorem three_dvd_card_of_trialityD4_two
    {X : Type} [Group X] {n : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 2 n) : 3 ∣ Nat.card X := by
  rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h]
  show 3 ∣ CFSG.Open.ordTrialityD4 (2 ^ n)
  rw [CFSG.Open.ordTrialityD4]
  exact Dvd.dvd.mul_left (three_dvd_sq_sub_one (not_three_dvd_two_pow n)) _

theorem not_three_dvd_card_of_suzukiModel {X : Type} [Group X] {n : ℕ}
    (h : SuzukiModel X 2 n) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨e⟩⟩ := h
  subst hn
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have hq3' : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  set q := 2 ^ (2 * a + 1)
  have hq3 : q % 3 = 2 := hq3'
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq3]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h' | h'
    · have := Nat.mod_eq_zero_of_dvd h'
      omega
    · have := Nat.mod_eq_zero_of_dvd h'
      omega
  · have := Nat.mod_eq_zero_of_dvd h
    omega

end CFSG.Quasithin.F134
