module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Timmesfeld.ClassicalOrders

theorem card_statedProj_statedSL_mul_gcd {K : Type} [Field K] [Finite K] {a : ℕ} (ha : 2 ≤ a) :
    Nat.card (StatedProj (StatedSL a K)) * Nat.gcd a (Nat.card K - 1) =
      Nat.card K ^ (a * (a - 1) / 2) * ∏ j ∈ Finset.Icc 2 a, (Nat.card K ^ j - 1) := by
  rw [card_statedProj_statedSL (by omega)]
  refine Nat.div_mul_cancel ?_
  refine (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _)
  have h2 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
  exact h2.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, ha⟩))

theorem two_pow_sub_one_odd {m : ℕ} (hm : 1 ≤ m) : ¬ 2 ∣ 2 ^ m - 1 := by
  intro h
  have h1 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h3 : 2 ∣ 2 ^ m - (2 ^ m - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  omega

theorem prod_two_pow_sub_one_odd {f a : ℕ} (hf : 1 ≤ f) :
    ¬ 2 ∣ ∏ j ∈ Finset.Icc 2 a, ((2 ^ f) ^ j - 1) := by
  intro h
  obtain ⟨j, hj, hdvd⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).mp h
  rw [← pow_mul] at hdvd
  exact two_pow_sub_one_odd (by nlinarith [(Finset.mem_Icc.mp hj).1]) hdvd

theorem padicValNat_two_card_statedProj {K : Type} [Field K] [Finite K] {a f : ℕ} (ha : 2 ≤ a)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    padicValNat 2 (Nat.card (StatedProj (StatedSL a K))) = f * (a * (a - 1) / 2) := by
  have h := card_statedProj_statedSL_mul_gcd (K := K) ha
  have hpos : 0 < Nat.card (StatedProj (StatedSL a K)) := Nat.card_pos
  have hg : ¬ 2 ∣ Nat.gcd a (Nat.card K - 1) := fun h2 =>
    two_pow_sub_one_odd hf (hK ▸ h2.trans (Nat.gcd_dvd_right _ _))
  have hgpos : 0 < Nat.gcd a (Nat.card K - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hO := prod_two_pow_sub_one_odd (a := a) hf
  rw [hK] at h hg hgpos
  have hOpos : 0 < ∏ j ∈ Finset.Icc 2 a, ((2 ^ f) ^ j - 1) := by
    by_contra h0
    apply hO
    rw [Nat.eq_zero_of_not_pos h0]
    exact dvd_zero 2
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul hpos.ne' hgpos.ne', padicValNat.mul (by positivity) hOpos.ne',
    padicValNat.eq_zero_of_not_dvd hg, padicValNat.eq_zero_of_not_dvd hO, ← pow_mul,
    padicValNat.prime_pow] at hv
  simpa using hv

theorem exists_primitive_prime_dvd_card_statedProj {K : Type} [Field K] [Finite K] {a f : ℕ}
    (ha : 2 ≤ a) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (h6 : f * a ≠ 6) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card (StatedProj (StatedSL a K)) ∧ ¬ r ∣ 2 ∧
      ∀ k : ℕ, 0 < k → k < f * a → ¬ r ∣ 2 ^ k - 1 := by
  obtain ⟨r, hr, hrd, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (f * a) (by nlinarith) h6
  have hr2 : ¬ r ∣ 2 := by
    intro h2
    have hr2' : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    rw [hr2'] at hrd
    exact two_pow_sub_one_odd (by nlinarith) hrd
  refine ⟨r, hr, ?_, hr2, hprim⟩
  have h := card_statedProj_statedSL_mul_gcd (K := K) ha
  have hdvd : r ∣ Nat.card (StatedProj (StatedSL a K)) * Nat.gcd a (Nat.card K - 1) := by
    rw [h]
    refine Dvd.dvd.mul_left ?_ _
    refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨ha, le_rfl⟩))
    rw [hK, ← pow_mul]
    exact hrd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
  · exact h1
  · exfalso
    have h2 : r ∣ 2 ^ f - 1 := hK ▸ h1.trans (Nat.gcd_dvd_right _ _)
    exact hprim f (by omega) (by nlinarith) h2

theorem le_of_primitive_dvd_card_statedProj {K : Type} [Field K] [Finite K] {b g : ℕ}
    (hb : 2 ≤ b) (hg : 1 ≤ g) (hK : Nat.card K = 2 ^ g) {r n : ℕ} (hr : r.Prime) (hr2 : ¬ r ∣ 2)
    (hrd : r ∣ Nat.card (StatedProj (StatedSL b K)))
    (hprim : ∀ k : ℕ, 0 < k → k < n → ¬ r ∣ 2 ^ k - 1) : n ≤ g * b := by
  have h := card_statedProj_statedSL_mul_gcd (K := K) hb
  have hdvd : r ∣ Nat.card K ^ (b * (b - 1) / 2) * ∏ j ∈ Finset.Icc 2 b, (Nat.card K ^ j - 1) := by
    rw [← h]
    exact Dvd.dvd.mul_right hrd _
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
  · exfalso
    rw [hK, ← pow_mul] at h1
    exact hr2 (hr.dvd_of_dvd_pow h1)
  · obtain ⟨j, hj, hdvdj⟩ := (hr.prime.dvd_finset_prod_iff _).mp h1
    rw [hK, ← pow_mul] at hdvdj
    have hj' := Finset.mem_Icc.mp hj
    by_contra hlt
    push Not at hlt
    exact hprim (g * j) (by nlinarith) (by nlinarith) hdvdj

theorem card_statedProj_ne_of_eight_two {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    (hK : Nat.card K = 8) (hK' : Nat.card K' = 2) :
    Nat.card (StatedProj (StatedSL 2 K)) ≠ Nat.card (StatedProj (StatedSL 3 K')) := by
  have e1 := card_statedProj_statedSL_mul_gcd (K := K) (a := 2) le_rfl
  have e2 := card_statedProj_statedSL_mul_gcd (K := K') (a := 3) (by norm_num)
  rw [hK] at e1
  rw [hK'] at e2
  have p1 : (∏ j ∈ Finset.Icc 2 2, ((8 : ℕ) ^ j - 1)) = 63 := by decide
  have p2 : (∏ j ∈ Finset.Icc 2 3, ((2 : ℕ) ^ j - 1)) = 21 := by decide
  rw [p1] at e1
  rw [p2] at e2
  norm_num at e1 e2
  omega

theorem artin_arith {a b f g : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hval : f * (a * (a - 1) / 2) = g * (b * (b - 1) / 2))
    (hle1 : f * a ≠ 6 → f * a ≤ g * b) (hle2 : g * b ≠ 6 → g * b ≤ f * a) :
    (a = b ∧ f = g) ∨ (a = 3 ∧ f = 2 ∧ b = 4 ∧ g = 1) ∨ (a = 4 ∧ f = 1 ∧ b = 3 ∧ g = 2) ∨
      (a = 2 ∧ f = 3 ∧ b = 3 ∧ g = 1) ∨ (a = 3 ∧ f = 1 ∧ b = 2 ∧ g = 3) := by
  by_cases h6 : f * a = 6
  · have ha6 : a ≤ 6 := by nlinarith
    have hf6 : f ≤ 3 := by nlinarith
    have hgb : g * b ≤ 6 := by
      by_cases h6' : g * b = 6
      · omega
      · exact hle2 h6' |>.trans h6.le
    have hb6 : b ≤ 6 := by nlinarith
    have hg6 : g ≤ 3 := by nlinarith
    interval_cases a <;> interval_cases f <;> (try omega) <;> interval_cases b <;>
      interval_cases g <;> omega
  · by_cases h6' : g * b = 6
    · have hb6 : b ≤ 6 := by nlinarith
      have hg6 : g ≤ 3 := by nlinarith
      have hfa : f * a ≤ 6 := (hle1 h6).trans h6'.le
      have ha6 : a ≤ 6 := by nlinarith
      have hf6 : f ≤ 3 := by nlinarith
      interval_cases a <;> interval_cases f <;> (try omega) <;> interval_cases b <;>
        interval_cases g <;> omega
    · left
      have hfg : f * a = g * b := le_antisymm (hle1 h6) (hle2 h6')
      have hA : a * (a - 1) / 2 * 2 = a * (a - 1) :=
        Nat.div_mul_cancel (Nat.even_mul_pred_self a).two_dvd
      have hB : b * (b - 1) / 2 * 2 = b * (b - 1) :=
        Nat.div_mul_cancel (Nat.even_mul_pred_self b).two_dvd
      have h1 : f * a * (a - 1) = g * b * (b - 1) := by
        have := congrArg (· * 2) hval
        nlinarith [hA, hB]
      rw [hfg] at h1
      have hpos : 0 < g * b := by positivity
      have hab : a - 1 = b - 1 := Nat.eq_of_mul_eq_mul_left hpos h1
      have hab' : a = b := by omega
      subst hab'
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) hfg⟩

theorem artinLinearOrders_holds : ArtinLinearOrdersStatement := by
  intro a b K K' _ _ _ _ ha hb ⟨f, hf, hK⟩ ⟨g, hg, hK'⟩ hnot hnot' hcard
  have hv := padicValNat_two_card_statedProj (K := K) ha hf hK
  have hv' := padicValNat_two_card_statedProj (K := K') hb hg hK'
  rw [hcard] at hv
  have hval : f * (a * (a - 1) / 2) = g * (b * (b - 1) / 2) := hv.symm.trans hv'
  have hle1 : f * a ≠ 6 → f * a ≤ g * b := fun h6 => by
    obtain ⟨r, hr, hrd, hr2, hprim⟩ :=
      exists_primitive_prime_dvd_card_statedProj (K := K) ha hf hK h6
    exact le_of_primitive_dvd_card_statedProj (K := K') hb hg hK' hr hr2
      (by rw [← hcard]; exact hrd) hprim
  have hle2 : g * b ≠ 6 → g * b ≤ f * a := fun h6 => by
    obtain ⟨r, hr, hrd, hr2, hprim⟩ :=
      exists_primitive_prime_dvd_card_statedProj (K := K') hb hg hK' h6
    exact le_of_primitive_dvd_card_statedProj (K := K) ha hf hK hr hr2
      (by rw [hcard]; exact hrd) hprim
  rcases artin_arith ha hb hf hg hval hle1 hle2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, hK.trans hK'.symm⟩
  · exact Or.inr (Or.inl ⟨rfl, by rw [hK]; norm_num, rfl, by rw [hK']; norm_num⟩)
  · exact Or.inr (Or.inr ⟨rfl, by rw [hK]; norm_num, rfl, by rw [hK']; norm_num⟩)
  · exact absurd hcard (card_statedProj_ne_of_eight_two (by rw [hK]; norm_num)
      (by rw [hK']; norm_num))
  · exact absurd hcard.symm (card_statedProj_ne_of_eight_two (by rw [hK']; norm_num)
      (by rw [hK]; norm_num))

end CFSG.RankThree.GF2n.Stroth80

end
