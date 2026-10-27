module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourDefs
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

private theorem eq_three_of_dvd_six {c : ℕ} (hodd : Odd c) (h1 : c ≠ 1) (h6 : c ∣ 6) : c = 3 := by
  obtain ⟨k, rfl⟩ := hodd
  have hle : 2 * k + 1 ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hk : k ≤ 2 := by omega
  interval_cases k
  · exact absurd rfl h1
  · rfl
  · exact absurd h6 (by decide)

private theorem false_of_lieModel_three_one {S : Type} [Group S] {t : StatedLieTag} {n : ℕ}
    (ht : t = .twistedB2 ∨ t = .twistedF4 ∨ t = .twistedG2 ∨ t = .Tits)
    (hm : LieModel S t n 3 1) : False := by
  obtain ⟨-, -, h⟩ := hm.admissible
  rcases ht with rfl | rfl | rfl | rfl <;> simp at h

private theorem involGood_of_tag {S : Type} [Group S] [Finite S]
    (hPSL : InvolAt .PSL) (hPSU : InvolAt .PSU) (hPSp : InvolAt .PSp)
    (hOdd : InvolAt .POmegaOdd) (hPlus : InvolAt .POmegaPlus) (hMinus : InvolAt .POmegaMinus)
    (hG2 : InvolGenG2) (hF4 : InvolAt .F4) (hE6 : InvolAt .E6) (hE7 : InvolAt .E7)
    (hE8 : InvolAt .E8) (h2E6 : InvolAt .twistedE6) (h3D4 : InvolAt .trialityD4)
    {t : StatedLieTag} {n : ℕ} (hm : LieModel S t n 3 1) (hU3 : ¬ (t = .PSU ∧ n = 3))
    (hP4 : ¬ (t = .PSp ∧ n = 2)) : InvolGood S := by
  cases t with
  | PSL => exact hPSL S n hU3 hP4 hm
  | PSU => exact hPSU S n hU3 hP4 hm
  | PSp => exact hPSp S n hU3 hP4 hm
  | POmegaOdd => exact hOdd S n hU3 hP4 hm
  | POmegaPlus => exact hPlus S n hU3 hP4 hm
  | POmegaMinus => exact hMinus S n hU3 hP4 hm
  | G2 =>
    obtain ⟨-, -, rfl, -⟩ := hm.admissible
    exact (hG2 S hm).involGood
  | F4 => exact hF4 S n hU3 hP4 hm
  | E6 => exact hE6 S n hU3 hP4 hm
  | E7 => exact hE7 S n hU3 hP4 hm
  | E8 => exact hE8 S n hU3 hP4 hm
  | twistedE6 => exact h2E6 S n hU3 hP4 hm
  | trialityD4 => exact h3D4 S n hU3 hP4 hm
  | twistedB2 => exact (false_of_lieModel_three_one (Or.inl rfl) hm).elim
  | twistedF4 => exact (false_of_lieModel_three_one (Or.inr (Or.inl rfl)) hm).elim
  | twistedG2 => exact (false_of_lieModel_three_one (Or.inr (Or.inr (Or.inl rfl))) hm).elim
  | Tits => exact (false_of_lieModel_three_one (Or.inr (Or.inr (Or.inr rfl))) hm).elim


theorem center_cases_three (hGA : GriessAllModelsStatement) {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hLq : CFSG.IsQuasisimple ↥L) (hO2 : O2Trivial L)
    {t : StatedLieTag} {n : ℕ} (hm : LieModel (↥L ⧸ center ↥L) t n 3 1) :
    center ↥L = ⊥ ∨ ((t = .G2 ∨ (t = .POmegaOdd ∧ n = 3)) ∧ Nat.card (center ↥L) = 3) ∨
      (t = .PSU ∧ n = 4 ∧ center ↥L ≠ ⊥) := by
  by_cases hZ : center ↥L = ⊥
  · exact Or.inl hZ
  right
  have hodd := W4Row.odd_card_center_of_o2Trivial hO2
  have hdvd := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA hLq
    (MulEquiv.refl _) (CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hm)
  have hne1 : Nat.card (center ↥L) ≠ 1 := fun h => hZ (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨p, hp, hpZ⟩ := Nat.exists_prime_and_dvd hne1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hpZ)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  rcases CFSG.HardMathSupport.Timmesfeld.Tables.T1b.case_of_dvd_table hp hp2 (hpZ.trans hdvd) with
    ⟨-, hd⟩ | ⟨-, hd⟩ | ⟨⟨-, -, hd⟩ | ⟨-, -, hd⟩⟩ | ⟨-, hcases⟩
  · exact absurd (by simpa using hd.trans (Nat.gcd_dvd_right _ _)) hp2'
  · have h4 : p ∣ 4 := by simpa using hd.trans (Nat.gcd_dvd_right _ _)
    exact absurd (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)) hp2'
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · rcases hcases with ⟨-, -, -, h⟩ | ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -, -⟩
    · omega
    · exact Or.inl ⟨Or.inr ⟨rfl, rfl⟩, eq_three_of_dvd_six hodd hne1 (hdvd.trans (by decide))⟩
    · exact Or.inl ⟨Or.inl rfl, eq_three_of_dvd_six hodd hne1 (hdvd.trans (by decide))⟩
    · exact Or.inr ⟨rfl, rfl, hZ⟩

theorem w4Lem10_5ResidualThree_of (hGA : GriessAllModelsStatement)
    (hPSL : InvolAt .PSL) (hPSU : InvolAt .PSU) (hPSp : InvolAt .PSp)
    (hOdd : InvolAt .POmegaOdd) (hPlus : InvolAt .POmegaPlus) (hMinus : InvolAt .POmegaMinus)
    (hG2 : InvolGenG2) (hF4 : InvolAt .F4) (hE6 : InvolAt .E6) (hE7 : InvolAt .E7)
    (hE8 : InvolAt .E8) (h2E6 : InvolAt .twistedE6) (h3D4 : InvolAt .trialityD4)
    (hOm : OmegaSevenCover) : W4Lem10_5ResidualThree := by
  intro W _ _ hW Y L t n hLY hLn hF hLq hO2 hm hU3 hP4 hU4
  have : Finite (MulAut W) := MulEquiv.finite_left
  rcases center_cases_three hGA hLq hO2 hm with hZ | ⟨ht, hZ3⟩ | ⟨rfl, rfl, hZ⟩
  · exact four_le_mParam_of_involGood hW hLY hLn hF hLq hO2 hZ
      (involGood_of_tag hPSL hPSU hPSp hOdd hPlus hMinus hG2 hF4 hE6 hE7 hE8 h2E6 h3D4 hm hU3 hP4)
  · rcases ht with rfl | ⟨rfl, rfl⟩
    · obtain ⟨-, -, rfl, -⟩ := hm.admissible
      exact four_le_mParam_of_involGen hW hLY hLn hF hLq hO2 ⟨1, by rw [hZ3, pow_one]⟩
        (hG2 _ hm)
    · exact hOm W hW Y L hLY hLn hF hLq hO2 hm hZ3
  · exact absurd ⟨rfl, rfl, hZ⟩ hU4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
