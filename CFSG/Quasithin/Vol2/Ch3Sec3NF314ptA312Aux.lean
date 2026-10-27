module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312Excl
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.H13.InspA312

theorem card_psl32 {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 3 2 1 h).1]
  decide

theorem card_psl42 {X : Type} [Group X] (h : IsPSL 4 2 1 X) : Nat.card X = 20160 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 4 2 1 h).1]
  decide

theorem card_psl52 {X : Type} [Group X] (h : IsPSL 5 2 1 X) : Nat.card X = 9999360 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 5 2 1 h).1]
  decide

theorem card_psl34 {X : Type} [Group X] (h : IsPSL 3 2 2 X) : Nat.card X = 20160 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 3 2 2 h).1]
  decide

theorem card_psl2_odd {X : Type} [Group X] {q : ℕ} (h : IsPSL 2 q 1 X) (hq : q % 2 = 1) :
    Nat.card X = q * (q ^ 2 - 1) / 2 := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 2 q 1 h).1
  have hg : Nat.gcd 2 (q ^ 1 - 1) = 2 := Nat.gcd_eq_left (by rw [pow_one]; omega)
  rw [hb, hg, show Finset.Icc 2 2 = {2} from rfl, Finset.prod_singleton]
  norm_num

theorem card_psl2_sq {X : Type} [Group X] {q : ℕ} (h : IsPSL 2 q 2 X) (hq : q % 2 = 1) :
    Nat.card X = q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2 := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 2 q 2 h).1
  have hsq : q ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hq]
  have hg : Nat.gcd 2 (q ^ 2 - 1) = 2 := Nat.gcd_eq_left (by omega)
  rw [hb, hg, show Finset.Icc 2 2 = {2} from rfl, Finset.prod_singleton]
  norm_num

theorem card_psl2_seven_sq {X : Type} [Group X] (h : IsPSL 2 7 2 X) : Nat.card X = 58800 := by
  rw [card_psl2_sq h (by norm_num)]
  norm_num

theorem card_sl2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (h : CFSG.Quasithin.IsSL2 p X) :
    Nat.card X = p * (p ^ 2 - 1) := by
  obtain ⟨e⟩ := h
  haveI := Fact.mk hp
  rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]

theorem card_alt5 {X : Type} [Group X] (h : IsAlt 5 X) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide

theorem card_alt6 {X : Type} [Group X] (h : IsAlt 6 X) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide

theorem card_alt7 {X : Type} [Group X] (h : IsAlt 7 X) : Nat.card X = 2520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide

theorem card_hat {X S : Type} [Group X] [Group S] (h : CFSG.Quasithin.IsHat X S) :
    Nat.card X = 3 * Nat.card S := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have hm := Subgroup.card_mul_index (Subgroup.center X)
  rw [hc] at hm
  rw [← hm, Subgroup.index, Nat.card_congr e.toEquiv]

theorem card_M22 {X : Type} [Group X]
    (h : CFSG.Quasithin.IsSporadic .M22 X) : Nat.card X = 443520 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  rw [Nat.card_congr e.toEquiv, this]

theorem card_J4 {X : Type} [Group X]
    (h : CFSG.Quasithin.IsSporadic .J4 X) : Nat.card X = 86775571046077562880 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  rw [Nat.card_congr e.toEquiv, this]

theorem card_dvd_of_surj {G S : Type} [Group G] [Group S] (f : G →* S)
    (hf : Function.Surjective f) : Nat.card S ∣ Nat.card G := by
  have hS : Nat.card S = f.ker.index := by
    rw [Subgroup.index]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm
  rw [hS]
  exact Subgroup.index_dvd_card _

theorem card_multiplicative_fin_zmod (p n : ℕ) [Fact p.Prime] :
    Nat.card (Multiplicative (Fin n → ZMod p)) = p ^ n := by
  rw [← Nat.card_congr (Multiplicative.ofAdd : (Fin n → ZMod p) ≃ Multiplicative (Fin n → ZMod p)),
    Nat.card_pi]
  simp [Nat.card_zmod]

theorem mod_eight_L2 {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) : q * (q ^ 2 - 1) / 2 % 8 = 4 := by
  have h := CFSG.Quasithin.H13.InspA312.ordProj_two_card_L2_of_mod_eight hq
  have hN : q * (q ^ 2 - 1) / 2 ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have h1 := Nat.ordProj_mul_ordCompl_eq_self (q * (q ^ 2 - 1) / 2) 2
  have h2 := Nat.coprime_ordCompl Nat.prime_two hN
  rw [h] at h1 h2
  obtain ⟨j, hj⟩ := Nat.coprime_two_left.mp h2
  generalize q * (q ^ 2 - 1) / 2 = N at h1 hj ⊢
  omega

theorem mod_sixteen_L2 {Q : ℕ} (hQ : Q ^ 2 % 32 = 17) : Q * (Q ^ 2 - 1) / 2 % 16 = 8 := by
  have h := CFSG.Quasithin.H13.InspA312.ordProj_two_card_L2_of_sq_mod hQ
  have hN : Q * (Q ^ 2 - 1) / 2 ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have h1 := Nat.ordProj_mul_ordCompl_eq_self (Q * (Q ^ 2 - 1) / 2) 2
  have h2 := Nat.coprime_ordCompl Nat.prime_two hN
  rw [h] at h1 h2
  obtain ⟨j, hj⟩ := Nat.coprime_two_left.mp h2
  generalize Q * (Q ^ 2 - 1) / 2 = N at h1 hj ⊢
  omega

theorem le_card_L2_eleven {q : ℕ} (hq : 11 ≤ q) : 660 ≤ q * (q ^ 2 - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : 120 ≤ q ^ 2 - 1 := by
    have : 121 ≤ q ^ 2 := by nlinarith
    omega
  calc 660 * 2 = 11 * 120 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq h1

theorem three_dvd_card_L2 {q : ℕ} (hq : q % 2 = 1) : 3 ∣ q * (q ^ 2 - 1) / 2 := by
  have hsq : q ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hq]
  have h2 : 2 ∣ q * (q ^ 2 - 1) := Dvd.dvd.mul_left (by omega) q
  have h3 := CFSG.Quasithin.F134.three_dvd_mul_sq_sub_one q
  have e := Nat.div_mul_cancel h2
  generalize q * (q ^ 2 - 1) / 2 = N at e ⊢
  omega

theorem eight_dvd_sl2 {p : ℕ} (hp : p % 2 = 1) : 8 ∣ p * (p ^ 2 - 1) := by
  have h8 : p ^ 2 % 8 = 1 := by
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
  exact Dvd.dvd.mul_left (by omega) p

theorem mul_sq_sub_one_eq_two_mul {p m : ℕ} (hp : p % 2 = 1) (h : p * (p ^ 2 - 1) / 2 = m) :
    p * (p ^ 2 - 1) = 2 * m := by
  have h2 : 2 ∣ p * (p ^ 2 - 1) := Dvd.dvd.trans (by norm_num) (eight_dvd_sl2 hp)
  rw [← h, Nat.mul_div_cancel' h2]

theorem mul_lt_mul_aux {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 < b ^ 2 := by nlinarith
  have h2 : 1 ≤ a ^ 2 := by nlinarith
  have h3 : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h4 : a * (a ^ 2 - 1) ≤ b * (a ^ 2 - 1) := Nat.mul_le_mul hab.le le_rfl
  have h5 : b * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    apply Nat.mul_lt_mul_of_pos_left h3
    omega
  omega

theorem eq_of_mul_sq_sub_one_eq {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : p * (p ^ 2 - 1) = q * (q ^ 2 - 1)) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exfalso
    have := mul_lt_mul_aux (by omega) hlt
    omega
  · exact heq
  · exfalso
    have := mul_lt_mul_aux (by omega) hgt
    omega

theorem coprime_of_small {q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) (a b c d : ℕ) :
    Nat.Coprime q (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) := by
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).mpr (by omega))
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_three).mpr (by omega))
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq (by norm_num)).mpr (by omega))
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq (by norm_num)).mpr (by omega))

theorem not_dvd_2520 {q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) : ¬ q ∣ 2520 := by
  intro h
  have hc : Nat.Coprime q 2520 := by
    rw [show (2520 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num]
    exact coprime_of_small hq hq11 3 2 1 1
  have := Nat.Coprime.eq_one_of_dvd hc h
  omega

theorem not_dvd_7560 {q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) : ¬ q ∣ 7560 := by
  intro h
  have hc : Nat.Coprime q 7560 := by
    rw [show (7560 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 by norm_num]
    exact coprime_of_small hq hq11 3 3 1 1
  have := Nat.Coprime.eq_one_of_dvd hc h
  omega

theorem two_pow_card_ne_168 {n : ℕ} (hn : 2 ≤ n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 := by
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · norm_num
  · norm_num
  · have h16 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    have h255 : 255 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    intro h
    have := Nat.mul_le_mul h16 h255
    omega

theorem two_pow_card_ne_of_mod_eight {n N : ℕ} (hn : 2 ≤ n) (hN8 : N % 8 = 4) (hN : 660 ≤ N) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ N := by
  intro h
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · norm_num at h
    omega
  · have h8 : 8 ∣ 2 ^ n := by
      have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 h3
      norm_num at this
      exact this
    have h8' : 8 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Dvd.dvd.mul_right h8 _
    rw [h] at h8'
    omega

end CFSG.Quasithin.H13.NF314ptA312
