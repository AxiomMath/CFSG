module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Arith

private lemma endgH_pow5_mod24 (k : ℕ) : 5 ^ k % 24 = 1 ∨ 5 ^ k % 24 = 5 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

private lemma endgH_sq_mod24 (b : ℕ) (hb : 2 ≤ b) : ((2 ^ b) ^ 2 + 1) % 24 = 17 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  have h3 : 4 ^ c % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have e : (2 ^ (c + 2)) ^ 2 = 16 * 4 ^ c := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    ring
  rw [e]
  omega

private lemma endgH_ne_pow5 (b : ℕ) (hb : 2 ≤ b) (k : ℕ) : (2 ^ b) ^ 2 + 1 ≠ 5 ^ k := by
  intro h
  have h1 := endgH_sq_mod24 b hb
  have h2 := endgH_pow5_mod24 k
  rw [← h] at h2
  generalize (2 ^ b) ^ 2 + 1 = N at h1 h2
  omega

private lemma endgH_exists_prime (b : ℕ) (hb : 2 ≤ b) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 5 ∧ p ∣ (2 ^ b) ^ 2 + 1 := by
  by_contra hcon
  push_neg at hcon
  have hN : (2 ^ b) ^ 2 + 1 ≠ 0 := by positivity
  have hfac := Nat.eq_prime_pow_of_unique_prime_dvd hN (p := 5)
    (fun {d} hd hdvd => by
      by_contra hne
      exact hcon d hd hne hdvd)
  exact endgH_ne_pow5 b hb _ hfac

private lemma endgH_num {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (h1 : p % 4 = 1) :
    13 ≤ p := by
  by_contra hlt
  push_neg at hlt
  interval_cases p <;> first | omega | norm_num at hp

private lemma endgH_ge13 {p b : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (hb : 2 ≤ b)
    (hpd : p ∣ (2 ^ b) ^ 2 + 1) : 13 ≤ p := by
  haveI := Fact.mk hp
  have hz : ((2 : ZMod p) ^ b) ^ 2 + 1 = 0 := by
    have h := (CharP.cast_eq_zero_iff (ZMod p) p _).2 hpd
    push_cast at h
    exact h
  have h4 : p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := (2 : ZMod p) ^ b) (by linear_combination hz)
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · rw [h2] at hpd
      have h2b : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega)
      have h2sq : 2 ∣ (2 ^ b) ^ 2 := dvd_pow h2b (by norm_num)
      omega
    · exact h2
  exact endgH_num hp hp5 (by omega)

private lemma endgH_two_ne {p : ℕ} [Fact p.Prime] (h13 : 13 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have h'' := (CharP.cast_eq_zero_iff (ZMod p) p 2).1 h'
  have := Nat.le_of_dvd (by norm_num) h''
  omega

private lemma endgH_three_ne {p : ℕ} [Fact p.Prime] (h13 : 13 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have h'' := (CharP.cast_eq_zero_iff (ZMod p) p 3).1 h'
  have := Nat.le_of_dvd (by norm_num) h''
  omega

private lemma endgH_facts {p : ℕ} [Fact p.Prime] (h13 : 13 ≤ p) {x : ZMod p}
    (hx : x ^ 2 + 1 = 0) :
    x ≠ 0 ∧ x ^ 2 - 1 ≠ 0 ∧ x ^ 3 - 1 ≠ 0 ∧ x ^ 6 - 1 ≠ 0 ∧ x ^ 8 + x ^ 4 + 1 ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := endgH_two_ne h13
  have h3 : (3 : ZMod p) ≠ 0 := endgH_three_ne h13
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hx
    norm_num at hx
  · intro h
    apply h2
    linear_combination hx - h
  · intro h
    have hx1 : x + 1 = 0 := by linear_combination x * hx - h
    apply h2
    linear_combination hx - (x - 1) * hx1
  · intro h
    apply h2
    linear_combination (x ^ 4 - x ^ 2 + 1) * hx - h
  · intro h
    apply h3
    linear_combination h - (x ^ 4 + 2) * (x ^ 2 - 1) * hx

private lemma endgH_zmod_sq {p q : ℕ} (hpd : p ∣ q ^ 2 + 1) : (q : ZMod p) ^ 2 + 1 = 0 := by
  have h := (CharP.cast_eq_zero_iff (ZMod p) p _).2 hpd
  push_cast at h
  exact h

private lemma endgH_ordA {p q : ℕ} (hp : p.Prime) (h13 : 13 ≤ p) (hq : 1 ≤ q)
    (hpd : p ∣ q ^ 2 + 1) : ¬ p ∣ CFSG.Open.ordA 2 q := by
  haveI := Fact.mk hp
  obtain ⟨F1, F2, F3, -, -⟩ := endgH_facts h13 (endgH_zmod_sq hpd)
  have hsub : q - 1 ∣ q ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow q 1 2
    rwa [one_pow] at h
  have hmem : (2 : ℕ) ∈ Finset.Icc 2 (2 + 1) := Finset.mem_Icc.2 ⟨le_refl 2, by norm_num⟩
  have hprod : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 (2 + 1), (q ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem
  have hg : Nat.gcd (2 + 1) (q - 1) ∣
      q ^ (2 * (2 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (2 + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (dvd_trans (Nat.gcd_dvd_right _ _) (dvd_trans hsub hprod)) _
  intro h
  have hX : p ∣ q ^ (2 * (2 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (2 + 1), (q ^ i - 1) :=
    dvd_trans h (Nat.div_dvd_of_dvd hg)
  rcases (Nat.Prime.dvd_mul hp).1 hX with h1 | h1
  · exact F1 ((CharP.cast_eq_zero_iff (ZMod p) p q).2 (hp.dvd_of_dvd_pow h1))
  · obtain ⟨i, hi, hdi⟩ := (_root_.Prime.dvd_finsetProd_iff hp.prime _).1 h1
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    have hi3 : i ≤ 3 := by omega
    have hdi' : p ∣ q ^ i - 1 := hdi
    have hqi : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
    have hz := (CharP.cast_eq_zero_iff (ZMod p) p _).2 hdi'
    rw [Nat.cast_sub hqi, Nat.cast_pow, Nat.cast_one] at hz
    interval_cases i
    · exact F2 hz
    · exact F3 hz

private lemma endgH_ordG2 {p q : ℕ} (hp : p.Prime) (h13 : 13 ≤ p) (hq : 1 ≤ q)
    (hpd : p ∣ q ^ 2 + 1) : ¬ p ∣ CFSG.Open.ordG2 q := by
  haveI := Fact.mk hp
  obtain ⟨F1, F2, -, F4, -⟩ := endgH_facts h13 (endgH_zmod_sq hpd)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  intro h
  have h' : p ∣ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := h
  have hz := (CharP.cast_eq_zero_iff (ZMod p) p _).2 h'
  push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at hz
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 6 F1) F4) F2 hz

private lemma endgH_ordTD4 {p q : ℕ} (hp : p.Prime) (h13 : 13 ≤ p) (hq : 1 ≤ q)
    (hpd : p ∣ q ^ 2 + 1) : ¬ p ∣ CFSG.Open.ordTrialityD4 q := by
  haveI := Fact.mk hp
  obtain ⟨F1, F2, -, F4, F6⟩ := endgH_facts h13 (endgH_zmod_sq hpd)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  intro h
  have h' : p ∣ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := h
  have hz := (CharP.cast_eq_zero_iff (ZMod p) p _).2 h'
  push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at hz
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 F1) F6) F4) F2 hz

private lemma endgH_le7 {p a b c d : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    p ≤ 7 := by
  have key : ∀ x e : ℕ, p ∣ x ^ e → 0 < x → x ≤ 7 → p ≤ 7 := by
    intro x e h0 hx hx7
    exact le_trans (Nat.le_of_dvd hx (hp.dvd_of_dvd_pow h0)) hx7
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact key 2 a h3 (by norm_num) (by norm_num)
      · exact key 3 b h3 (by norm_num) (by norm_num)
    · exact key 5 c h2 (by norm_num) (by norm_num)
  · exact key 7 d h1 (by norm_num) (by norm_num)

theorem endg_arith (b : ℕ) (hb : 2 ≤ b) :
    ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧ p ∣ (2 ^ b) ^ 2 + 1 ∧
      ¬ p ∣ CFSG.Open.ordA 2 (2 ^ b) ∧ ¬ p ∣ CFSG.Open.ordG2 (2 ^ b) ∧
      ¬ p ∣ CFSG.Open.ordTrialityD4 (2 ^ b) ∧ ¬ p ∣ 6048 ∧ ¬ p ∣ 360 ∧ ¬ p ∣ 604800 := by
  obtain ⟨p, hp, hp5, hpd⟩ := endgH_exists_prime b hb
  have h13 : 13 ≤ p := endgH_ge13 hp hp5 hb hpd
  have hq : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨p, hp, h13, hpd, endgH_ordA hp h13 hq hpd, endgH_ordG2 hp h13 hq hpd,
    endgH_ordTD4 hp h13 hq hpd, ?_, ?_, ?_⟩
  · intro h
    rw [show (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 5 ^ 0 * 7 ^ 1 by norm_num] at h
    have := endgH_le7 hp h
    omega
  · intro h
    rw [show (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 ^ 1 * 7 ^ 0 by norm_num] at h
    have := endgH_le7 hp h
    omega
  · intro h
    rw [show (604800 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 ^ 1 by norm_num] at h
    have := endgH_le7 hp h
    omega

end Arith

end CFSG.RankThree.GF2n.Stroth80
