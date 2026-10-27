module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91CoreArith
import CFSG.Adapters.StatedSmallProjOrders
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Card
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.Quasithin.MS93.FFOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22


private theorem not_threeCover_center {X : Type} [Group X] [Finite X] {n : ℕ} (h : Is3D4 X n)
    (S : ∀ (Y : Type) [Group Y], Prop) :
    ¬ CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover S X := by
  rintro ⟨-, hZ, -⟩
  rw [(CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions
    (CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide))).1,
    Subgroup.card_bot] at hZ
  omega

private theorem not_psl3_of_lieModel {X : Type} [Group X] [Finite X] {n p f : ℕ}
    (hX : Is3D4 X n) (hLie : LieModel X .PSL 3 p f) : False := by
  have hn : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hX).2.1
  have hadm := CFSG.Blueprint.LieModel.admissible hLie
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hcardX : Nat.card X = ordTrialityD4 (2 ^ n) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide))
  by_cases hp2 : p = 2
  · rw [hp2] at hLie
    have hcard : Nat.card X = ordA 2 (2 ^ f) :=
      CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hLie
    exact CFSG.Quasithin.MS93.ordA_two_ne_ordTrialityD4 hf hn (hcard.symm.trans hcardX)
  · have hcard := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1.fl3_card_formula hp hf hp2 hLie
    have hr : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hr3 : 3 ≤ p ^ f := hp3.trans (le_self_pow (by omega) (by omega))
    have hd : Nat.gcd 3 (p ^ f - 1) ≤ 3 := Nat.gcd_le_left (p ^ f - 1) (by norm_num)
    exact R891Core.ordTrialityD4_two_pow_mul_ne_sl3 hn hr hr3 hd (by
      rw [← hcardX]
      exact hcard)

private theorem not_psu3_of_lieModel {X : Type} [Group X] [Finite X] {n p f : ℕ}
    (hX : Is3D4 X n) (hmod : p ^ f % 3 = 2) (hLie : LieModel X .PSU 3 p f) : False := by
  have hn : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hX).2.1
  have hadm := CFSG.Blueprint.LieModel.admissible hLie
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hcardX : Nat.card X = ordTrialityD4 (2 ^ n) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide))
  have hsc : CFSG.Open.StatedClassicalModel X .PSU 3 p f :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  have hcard := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three hsc
  by_cases hp2 : p = 2
  · rw [hp2] at hcard hmod
    have hgodd : Odd (Nat.gcd 3 (2 ^ f + 1)) :=
      Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 (2 ^ f + 1))
    have hqeven : Even (2 ^ f) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega : f ≠ 0)
    have hq2pos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow 2 (2 ^ f) (by positivity)
    have h1odd : Odd ((2 ^ f) ^ 2 - 1) :=
      Nat.Even.sub_odd hq2pos (hqeven.pow_of_ne_zero (by norm_num)) odd_one
    have h3odd : Odd ((2 ^ f) ^ 3 + 1) :=
      (hqeven.pow_of_ne_zero (by norm_num : 3 ≠ 0)).add_one
    have h1z : ((2 ^ f) ^ 2 - 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd => (Odd.ne_two_of_dvd_nat h1odd hd) rfl
    have h3z : ((2 ^ f) ^ 3 + 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd => (Odd.ne_two_of_dvd_nat h3odd hd) rfl
    have hgz : (Nat.gcd 3 (2 ^ f + 1)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd => (Odd.ne_two_of_dvd_nat hgodd hd) rfl
    have hR : ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))).factorization 2 =
        3 * f := by
      rw [Nat.factorization_mul (by positivity) (mul_ne_zero h1odd.pos.ne' h3odd.pos.ne'),
        Finsupp.add_apply, Nat.factorization_mul h1odd.pos.ne' h3odd.pos.ne',
        Finsupp.add_apply, h1z, h3z, add_zero, add_zero, Nat.factorization_pow,
        Finsupp.smul_apply, Nat.factorization_pow_self Nat.prime_two, smul_eq_mul]
    have hfac : (Nat.card X).factorization 2 = 3 * f := by
      have h := congrArg (fun m : ℕ => m.factorization 2) hcard
      rw [Nat.factorization_mul Nat.card_pos.ne' hgodd.pos.ne', Finsupp.add_apply, hgz,
        add_zero, hR] at h
      exact h
    have h12 : 3 * f = 12 * n := by
      rw [← hfac, hcardX, R891Core.factorization_two_ordTrialityD4_two_pow hn]
    have heven : Even f := ⟨2 * n, by omega⟩
    have hmod1 : 2 ^ f % 3 = 1 := by
      obtain ⟨k, rfl⟩ := heven
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    rw [hmod1] at hmod
    omega
  · have hr : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hr3 : 3 ≤ p ^ f := hp3.trans (le_self_pow (by omega) (by omega))
    have hd : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left (p ^ f + 1) (by norm_num)
    exact R891Core.ordTrialityD4_two_pow_mul_ne_su3 hn hr hr3 hd (by
      rw [← hcardX]
      exact hcard.trans (mul_assoc _ _ _).symm)

theorem r891NotSL3Core_holds : R891NotSL3Core := by
  intro X _ _ n hX hSL
  unfold IsSL3PiType at hSL
  rcases hSL with ⟨p, f, -, hLie⟩ | ⟨p, f, hmod, hLie⟩ | ⟨p, f, -, hcov⟩ | ⟨p, f, -, hcov⟩
  · exact not_psl3_of_lieModel hX hLie
  · exact not_psu3_of_lieModel hX hmod hLie
  · exact not_threeCover_center hX _ hcov
  · exact not_threeCover_center hX _ hcov

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
