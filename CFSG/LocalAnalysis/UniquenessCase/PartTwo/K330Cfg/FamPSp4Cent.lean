module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

private lemma k330c_seven_not_dvd_sq_add_one (q : ℕ) : ¬ 7 ∣ q ^ 2 + 1 := by
  intro h
  have hmod : (q ^ 2 + 1) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have hlt : q % 7 < 7 := Nat.mod_lt q (by norm_num)
  have hcases : q % 7 = 0 ∨ q % 7 = 1 ∨ q % 7 = 2 ∨ q % 7 = 3 ∨ q % 7 = 4 ∨
      q % 7 = 5 ∨ q % 7 = 6 := by omega
  rcases hcases with hc | hc | hc | hc | hc | hc | hc <;>
    · rw [Nat.add_mod, Nat.pow_mod, hc] at hmod
      norm_num at hmod

private lemma k330c_seven_not_dvd_ordBC_two (q : ℕ) (hq : ¬ 7 ∣ q) (h1 : ¬ 7 ∣ q ^ 2 - 1) :
    ¬ 7 ∣ ordBC 2 q := by
  intro h
  have hprod : (∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1)) =
      (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  have hN : ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) := by
    unfold ordBC
    rw [hprod]
  rw [hN] at h
  have hdvd : Nat.gcd 2 (q - 1) ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    have h1' : Nat.gcd 2 (q - 1) ∣ q ^ 2 - 1 := by
      refine dvd_trans (Nat.gcd_dvd_right 2 (q - 1)) ?_
      rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
        have := sq_tsub_sq q 1
        simpa [mul_comm] using this]
      exact dvd_mul_right (q - 1) (q + 1)
    have hinner : Nat.gcd 2 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 4 - 1) :=
      dvd_mul_of_dvd_left h1' (q ^ 4 - 1)
    simpa [mul_comm] using dvd_mul_of_dvd_left hinner (q ^ 4)
  have hmul : Nat.gcd 2 (q - 1) * 7 ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    (Nat.dvd_div_iff_mul_dvd hdvd).1 h
  have h7N : 7 ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    refine dvd_trans ?_ hmul
    simpa [mul_comm] using dvd_mul_right 7 (Nat.gcd 2 (q - 1))
  rw [Nat.prime_seven.dvd_mul] at h7N
  rcases h7N with hq4 | hrest
  · exact hq (Nat.prime_seven.dvd_of_dvd_pow hq4)
  · rw [Nat.prime_seven.dvd_mul] at hrest
    rcases hrest with h21 | h41
    · exact h1 h21
    · have hsq : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
        have := sq_tsub_sq (q ^ 2) 1
        simpa [show (q ^ 2) ^ 2 = q ^ 4 by ring, show (1 : ℕ) ^ 2 = 1 by norm_num]
          using this
      rw [hsq, Nat.prime_seven.dvd_mul] at h41
      rcases h41 with hplus | hminus
      · exact k330c_seven_not_dvd_sq_add_one q hplus
      · exact h1 hminus

private lemma k330c_noSevenCent_of_not_dvd_card {J : Type} [Group J] [Finite J]
    (h : ¬ 7 ∣ Nat.card J) : NoSevenCent J := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  intro X R _ _ _ hR hRne _
  have h7R : 7 ∣ Nat.card R := by
    rcases hR.card_eq_or_dvd with h1 | h7
    · exact absurd (Subgroup.eq_bot_of_card_eq R h1) hRne
    · exact h7
  exact h (h7R.trans (Subgroup.card_subgroup_dvd_card R))

theorem cent_PSp4 {J : Type} [Group J] [Finite J] {p f : ℕ} (e : LieModel J .PSp 2 p f)
    (hp : p ≠ 7) (h7 : ¬ 7 ∣ (p ^ f) ^ 2 - 1) : NoSevenCent J := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSp 2 p f :=
    CFSG.Blueprint.LieModel.admissible e
  have hpprime : p.Prime := hadm.1
  have hsc : CFSG.Open.StatedClassicalModel J .PSp 2 p f :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (n := 2) (by norm_num) e
  have hcard : Nat.card J = ordBC 2 (p ^ f) := by
    by_cases hp2 : p = 2
    · subst hp2
      exact (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.2.1 rfl
    · exact (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.1 rfl
  have hq : ¬ 7 ∣ p ^ f := by
    intro h
    have h7p : 7 ∣ p := Nat.prime_seven.dvd_of_dvd_pow h
    have h7eq : 7 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_seven hpprime).mp h7p
    exact hp h7eq.symm
  exact k330c_noSevenCent_of_not_dvd_card (by
    rw [hcard]
    exact k330c_seven_not_dvd_ordBC_two (p ^ f) hq h7)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
