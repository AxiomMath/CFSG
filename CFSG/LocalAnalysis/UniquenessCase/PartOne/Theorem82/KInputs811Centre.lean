module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt.GriessClassical

variable {Y : Type} [Group Y]

private theorem two_le_pow {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) : 2 ≤ r ^ f :=
  le_trans hr.two_le (Nat.le_self_pow (by omega) r)

private theorem five_le_of_prime_ne_two_ne_three {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2)
    (h3 : r ≠ 3) : 5 ≤ r := by
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two h2
  have := hr.two_le
  omega

private theorem five_le_pow_or_eq_four_of_prime_ne_three {r f : ℕ} (hr : r.Prime)
    (hr3 : r ≠ 3) (hf : 1 ≤ f) (h2 : r ^ f ≠ 2) : 5 ≤ r ^ f ∨ r ^ f = 4 := by
  by_cases hr2 : r = 2
  · subst hr2
    rcases f with _ | _ | _ | f
    · omega
    · exfalso; exact h2 (by norm_num)
    · exact Or.inr (by norm_num)
    · refine Or.inl ?_
      exact le_trans (by norm_num : (5 : ℕ) ≤ 2 ^ 3)
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 3 ≤ f + 3))
  · refine Or.inl ?_
    have hr5 := five_le_of_prime_ne_two_ne_three hr hr2 hr3
    exact le_trans hr5 (Nat.le_self_pow (by omega) r)

private theorem not_three_dvd_sub_one_of_mod_eq_two {m : ℕ} (h : m % 3 = 2) :
    ¬ 3 ∣ m - 1 := by
  rintro ⟨k, hk⟩
  have hmod : 3 * (m / 3) + 2 = m := by
    simpa [h] using Nat.div_add_mod m 3
  omega

private theorem not_three_dvd_add_one_of_mod_eq_one {m : ℕ} (h : m % 3 = 1) :
    ¬ 3 ∣ m + 1 := by
  rintro ⟨k, hk⟩
  have hmod : 3 * (m / 3) + 1 = m := by
    simpa [h] using Nat.div_add_mod m 3
  omega

private theorem gcd_six_dvd_two_of_not_three_dvd {m : ℕ} (h : ¬ 3 ∣ m) :
    Nat.gcd 6 m ∣ 2 := by
  have hnot : ¬ 3 ∣ Nat.gcd 6 m := fun hd => h (hd.trans (Nat.gcd_dvd_right 6 m))
  have hcop : Nat.Coprime (Nat.gcd 6 m) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hnot).symm
  have hdvd : Nat.gcd 6 m ∣ 2 * 3 := by simpa using Nat.gcd_dvd_left 6 m
  exact (hcop.dvd_mul_right).1 hdvd

private theorem card_generic_exceptional_eq (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]

private theorem center_eq_bot_of_dvd_two_pow (hodd : Odd (Nat.card (center Y))) {k : ℕ}
    (hdvd : Nat.card (center Y) ∣ 2 ^ k) : center Y = ⊥ := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (by
      rw [Nat.even_pow]
      exact ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact Subgroup.eq_bot_of_card_eq _ hj

private theorem card_center_dvd_of_multiplier_equiv {G : Type} [Group G] {M : ℕ}
    [Group.IsPerfect Y]
    (he : Nonempty (CFSG.Open.griessHopfMultiplier (Y ⧸ center Y) ≃* G))
    (hG : Nat.card G ∣ M) : Nat.card (center Y) ∣ M := by
  have h1 : Nat.card (center Y) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (Y ⧸ center Y)) :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (MulEquiv.refl (Y ⧸ center Y))
  rw [Nat.card_congr he.some.toEquiv] at h1
  exact h1.trans hG

private theorem center_eq_bot_of_isLie811_psp6
    {r f : ℕ} (h : IsLie811 Y .psp6 r f) (hsp : r ^ f ≠ 2) : center Y = ⊥ := by
  obtain ⟨hY, hodd, hr, hr3, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  have hf : 1 ≤ f := hm.admissible.2.1
  have hq := five_le_pow_or_eq_four_of_prime_ne_three hr hr3 hf hsp
  have hm' : Models.LieModel (Y ⧸ center Y) .PSp 3 r f :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
  obtain ⟨-, he⟩ := griess_classical_of_large .PSp hm'
    (Or.inr (Or.inr (Or.inl ⟨rfl, hq.elim Or.inl (fun h => Or.inr (Or.inl h))⟩)))
  have hexp : exceptionalOrders .PSp 3 r f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hgen : genericOrders .PSp 3 r f = (Nat.gcd 2 (r ^ f - 1), 1) := by simp [genericOrders]
  have hM : Nat.card (generic .PSp 3 r f × exceptional .PSp 3 r f) ∣ 2 := by
    rw [card_generic_exceptional_eq, hgen, hexp]
    simpa using Nat.gcd_dvd_left 2 (r ^ f - 1)
  exact center_eq_bot_of_dvd_two_pow hodd (k := 1) (by
    simpa using card_center_dvd_of_multiplier_equiv he hM)

private theorem center_eq_bot_of_isLie811_omega7
    {r f : ℕ} (h : IsLie811 Y .omega7 r f) : center Y = ⊥ := by
  obtain ⟨hY, hodd, hr, hr2, hr3, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  have hf : 1 ≤ f := hm.admissible.2.1
  have hr5 := five_le_of_prime_ne_two_ne_three hr hr2 hr3
  have hq : 5 ≤ r ^ f := le_trans hr5 (Nat.le_self_pow (by omega) r)
  have hm' : Models.LieModel (Y ⧸ center Y) .POmegaOdd 3 r f :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
  obtain ⟨-, he⟩ := griess_classical_of_large .POmegaOdd hm'
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl hq⟩))))
  have hexp : exceptionalOrders .POmegaOdd 3 r f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hgen : genericOrders .POmegaOdd 3 r f = (2, 1) := by simp [genericOrders]
  have hM : Nat.card (generic .POmegaOdd 3 r f × exceptional .POmegaOdd 3 r f) ∣ 2 := by
    rw [card_generic_exceptional_eq, hgen, hexp]
    norm_num
  exact center_eq_bot_of_dvd_two_pow hodd (k := 1) (by
    simpa using card_center_dvd_of_multiplier_equiv he hM)

private theorem center_eq_bot_of_isLie811_pomega8m
    {r f : ℕ} (h : IsLie811 Y .pomega8m r f) : center Y = ⊥ := by
  obtain ⟨hY, hodd, _hr, _hr3, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  have hm' : Models.LieModel (Y ⧸ center Y) .POmegaMinus 4 r f :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
  obtain ⟨-, he⟩ := griess_classical_of_large .POmegaMinus hm'
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hexp : exceptionalOrders .POmegaMinus 4 r f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hgen : genericOrders .POmegaMinus 4 r f = (Nat.gcd 4 ((r ^ f) ^ 4 + 1), 1) := by
    simp [genericOrders]
  have hM : Nat.card (generic .POmegaMinus 4 r f × exceptional .POmegaMinus 4 r f) ∣ 2 ^ 2 := by
    rw [card_generic_exceptional_eq, hgen, hexp]
    simpa using Nat.gcd_dvd_left 4 ((r ^ f) ^ 4 + 1)
  exact center_eq_bot_of_dvd_two_pow hodd (k := 2) (by
    simpa using card_center_dvd_of_multiplier_equiv he hM)

private theorem center_eq_bot_of_isLie811_l4
    {r f : ℕ} (h : IsLie811 Y .l4 r f) : center Y = ⊥ := by
  obtain ⟨hY, hodd, hr, hq2, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  rcases hm with ⟨h3, hm⟩ | ⟨h3, hm⟩
  · have hm' : Models.LieModel (Y ⧸ center Y) .PSL 4 r f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
    obtain ⟨-, he⟩ := griess_classical_of_large .PSL hm' (Or.inl rfl)
    have hexp : exceptionalOrders .PSL 4 r f = (1, 1) := by
      unfold exceptionalOrders; split <;> simp_all
    have hgen : genericOrders .PSL 4 r f = (Nat.gcd 4 (r ^ f - 1), 1) := by simp [genericOrders]
    have hM : Nat.card (generic .PSL 4 r f × exceptional .PSL 4 r f) ∣ 2 ^ 2 := by
      rw [card_generic_exceptional_eq, hgen, hexp]
      simpa using Nat.gcd_dvd_left 4 (r ^ f - 1)
    exact center_eq_bot_of_dvd_two_pow hodd (k := 2) (by
      simpa using card_center_dvd_of_multiplier_equiv he hM)
  · have hm' : Models.LieModel (Y ⧸ center Y) .PSU 4 r f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
    have hf : 1 ≤ f := hm.admissible.2.1
    have hq3 : r ^ f ≠ 3 := by
      intro hh
      rw [hh] at h3
      exact absurd h3 (by norm_num)
    have hq : 4 ≤ r ^ f := by
      have hge := two_le_pow hr hf
      omega
    obtain ⟨-, he⟩ := griess_classical_of_large .PSU hm'
      (Or.inr (Or.inl ⟨rfl, by decide, Or.inl hq⟩))
    have hexp : exceptionalOrders .PSU 4 r f = (1, 1) := by
      unfold exceptionalOrders; split <;> simp_all
    have hgen : genericOrders .PSU 4 r f = (Nat.gcd 4 (r ^ f + 1), 1) := by simp [genericOrders]
    have hM : Nat.card (generic .PSU 4 r f × exceptional .PSU 4 r f) ∣ 2 ^ 2 := by
      rw [card_generic_exceptional_eq, hgen, hexp]
      simpa using Nat.gcd_dvd_left 4 (r ^ f + 1)
    exact center_eq_bot_of_dvd_two_pow hodd (k := 2) (by
      simpa using card_center_dvd_of_multiplier_equiv he hM)

private theorem center_eq_bot_of_isLie811_l6
    {r f : ℕ} (h : IsLie811 Y .l6 r f) : center Y = ⊥ := by
  obtain ⟨hY, hodd, hr, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  rcases hm with ⟨h3, hm⟩ | ⟨h3, hm⟩
  · have hm' : Models.LieModel (Y ⧸ center Y) .PSL 6 r f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
    obtain ⟨-, he⟩ := griess_classical_of_large .PSL hm' (Or.inl rfl)
    have hexp : exceptionalOrders .PSL 6 r f = (1, 1) := by
      unfold exceptionalOrders; split <;> simp_all
    have hgen : genericOrders .PSL 6 r f = (Nat.gcd 6 (r ^ f - 1), 1) := by simp [genericOrders]
    have hg := gcd_six_dvd_two_of_not_three_dvd (not_three_dvd_sub_one_of_mod_eq_two h3)
    have hM : Nat.card (generic .PSL 6 r f × exceptional .PSL 6 r f) ∣ 2 := by
      rw [card_generic_exceptional_eq, hgen, hexp]
      simpa using hg
    exact center_eq_bot_of_dvd_two_pow hodd (k := 1) (by
      simpa using card_center_dvd_of_multiplier_equiv he hM)
  · have hm' : Models.LieModel (Y ⧸ center Y) .PSU 6 r f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
    have hf : 1 ≤ f := hm.admissible.2.1
    have hq2 : r ^ f ≠ 2 := by
      intro hh
      rw [hh] at h3
      exact absurd h3 (by norm_num)
    have hq3 : r ^ f ≠ 3 := by
      intro hh
      rw [hh] at h3
      exact absurd h3 (by norm_num)
    have hq : 4 ≤ r ^ f := by
      have hge := two_le_pow hr hf
      omega
    obtain ⟨-, he⟩ := griess_classical_of_large .PSU hm'
      (Or.inr (Or.inl ⟨rfl, by decide, Or.inl hq⟩))
    have hexp : exceptionalOrders .PSU 6 r f = (1, 1) := by
      unfold exceptionalOrders; split <;> simp_all
    have hgen : genericOrders .PSU 6 r f = (Nat.gcd 6 (r ^ f + 1), 1) := by simp [genericOrders]
    have hg := gcd_six_dvd_two_of_not_three_dvd (not_three_dvd_add_one_of_mod_eq_one h3)
    have hM : Nat.card (generic .PSU 6 r f × exceptional .PSU 6 r f) ∣ 2 := by
      rw [card_generic_exceptional_eq, hgen, hexp]
      simpa using hg
    exact center_eq_bot_of_dvd_two_pow hodd (k := 1) (by
      simpa using card_center_dvd_of_multiplier_equiv he hM)

theorem center_eq_bot_of_isLie811_of_ne
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) (hfam : fam ≠ .l7)
    (hsp : fam = .psp6 → r ^ f ≠ 2) : center Y = ⊥ := by
  rcases fam with _ | _ | _ | _ | _ | _
  · exact center_eq_bot_of_isLie811_psp6 h (hsp rfl)
  · exact center_eq_bot_of_isLie811_omega7 h
  · exact center_eq_bot_of_isLie811_pomega8m h
  · exact center_eq_bot_of_isLie811_l4 h
  · exact center_eq_bot_of_isLie811_l6 h
  · exact absurd rfl hfam

theorem center_eq_bot_of_isLie811_psp6_two
    {r f : ℕ} (h : IsLie811 Y .psp6 r f) (hq : r ^ f = 2) : center Y = ⊥ := by
  obtain ⟨hY, hodd, hr, -, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  have hf : 1 ≤ f := hm.admissible.2.1
  obtain ⟨rfl, rfl⟩ := GriessExceptionalPow.eq_two_one_of_pow_eq_two hr (by omega) hq
  have hm' : Models.LieModel (Y ⧸ center Y) .PSp 3 2 1 :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
  obtain ⟨-, he⟩ := psp_three_two_row hm'
  have hM : Nat.card (generic .PSp 3 2 1 × exceptional .PSp 3 2 1) ∣ 2 := by
    rw [card_generic_exceptional_eq]
    decide
  exact center_eq_bot_of_dvd_two_pow hodd (k := 1) (by
    simpa using card_center_dvd_of_multiplier_equiv he hM)

theorem center_eq_bot_of_isLie811
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) (hfam : fam ≠ .l7) :
    center Y = ⊥ := by
  by_cases hsp : fam = .psp6 ∧ r ^ f = 2
  · obtain ⟨hf, hq⟩ := hsp
    rw [hf] at h
    exact center_eq_bot_of_isLie811_psp6_two h hq
  · exact center_eq_bot_of_isLie811_of_ne h hfam (fun hf hq => hsp ⟨hf, hq⟩)

theorem card_center_dvd_of_isLie811_l7
    {r f : ℕ} (h : IsLie811 Y .l7 r f) :
    Nat.card (center Y) ∣ Nat.gcd 7 (qPlusPi r f) := by
  obtain ⟨hY, -, hr, hm⟩ := h
  haveI : Group.IsPerfect Y := hY.1
  rcases hm with ⟨h3, hm⟩ | ⟨h3, hm⟩
  · have hm' : Models.LieModel (Y ⧸ center Y) .PSL 7 r f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
    obtain ⟨-, he⟩ := griess_classical_of_large .PSL hm' (Or.inl rfl)
    have hexp : exceptionalOrders .PSL 7 r f = (1, 1) := by
      unfold exceptionalOrders; split <;> simp_all
    have hgen : genericOrders .PSL 7 r f = (Nat.gcd 7 (r ^ f - 1), 1) := by simp [genericOrders]
    have hq : qPlusPi r f = r ^ f - 1 := by
      unfold qPlusPi
      rw [if_neg (by omega)]
    have hM : Nat.card (generic .PSL 7 r f × exceptional .PSL 7 r f) ∣
        Nat.gcd 7 (qPlusPi r f) := by
      rw [card_generic_exceptional_eq, hgen, hexp, hq]
      simpa using dvd_rfl
    exact card_center_dvd_of_multiplier_equiv he hM
  · have hm' : Models.LieModel (Y ⧸ center Y) .PSU 7 r f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm
    obtain ⟨-, he⟩ := psu_odd_row
      (CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by decide) hm')
      (by decide : ¬ Even 7)
    have hexp : exceptionalOrders .PSU 7 r f = (1, 1) := exceptionalOrders_PSU_odd (by decide)
    have hgen : genericOrders .PSU 7 r f = (Nat.gcd 7 (r ^ f + 1), 1) := by simp [genericOrders]
    have hq : qPlusPi r f = r ^ f + 1 := by
      unfold qPlusPi
      rw [if_pos h3]
    have hM : Nat.card (generic .PSU 7 r f × exceptional .PSU 7 r f) ∣
        Nat.gcd 7 (qPlusPi r f) := by
      rw [card_generic_exceptional_eq, hgen, hexp, hq]
      simpa using dvd_rfl
    exact card_center_dvd_of_multiplier_equiv he hM

theorem not_three_dvd_card_center_of_isLie811
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) : ¬ 3 ∣ Nat.card (center Y) := by
  rcases eq_or_ne fam .l7 with hfam | hfam
  · subst hfam
    intro h3dvd
    have hdvd := card_center_dvd_of_isLie811_l7 h
    exact absurd (h3dvd.trans (hdvd.trans (Nat.gcd_dvd_left 7 (qPlusPi r f)))) (by norm_num)
  · rw [center_eq_bot_of_isLie811 h hfam, Subgroup.card_bot]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
