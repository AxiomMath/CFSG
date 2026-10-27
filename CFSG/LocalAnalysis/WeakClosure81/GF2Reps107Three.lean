module

import CFSG.GH74.Orders.LieType
import CFSG.GF2Type.Smith1980Orth.W4SigmaGL
import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)

private theorem w107_not_dvd_prod_two_pow (r : ℕ) (hr : r ≤ 6) :
    ¬ 3 ^ 6 ∣ ∏ i : Fin r, (2 ^ r - 2 ^ (i : ℕ)) := by
  interval_cases r <;> simp [Fin.prod_univ_succ]

theorem w107_three_pow_six_dvd {L : Type} [Group L] [Finite L]
    (h : LieModel (L ⧸ Subgroup.center L) .PSU 4 3 1) : 3 ^ 6 ∣ Nat.card L := by
  have hcard : Nat.card (L ⧸ Subgroup.center L) = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
    rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
      (by norm_num) (by norm_num) h]
    decide
  refine dvd_trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center L))
  rw [hcard]
  norm_num

theorem w107_not_three_pow_six_dvd_card_of_rk_le_six {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk W ≤ 6) (H : Subgroup (MulAut W)) :
    ¬ 3 ^ 6 ∣ Nat.card H := by
  intro hdiv
  let _ : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have : Fintype (Additive W) := Fintype.ofFinite _
  have hcardW : Nat.card W = 2 ^ rk W := by
    have h := card_eq_two_pow hW (⊤ : Subgroup W)
    rwa [Subgroup.card_top, rk_top] at h
  have hcardAdd : Nat.card (Additive W) = Nat.card W :=
    (Nat.card_congr (Additive.ofMul : W ≃ Additive W)).symm
  have hcardA : Nat.card (Additive W) = 2 ^ rk W := hcardAdd.trans hcardW
  have hcardV : Nat.card (Additive W) = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hfr : Module.finrank (ZMod 2) (Additive W) = rk W := by
    have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive W) = 2 ^ rk W := by
      rw [← hcardV, hcardA]
    exact Nat.pow_right_injective (a := 2) (by norm_num) h
  have hH : Nat.card H ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card H
  let ρ : MulAut W →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive W)).toMonoidHom.comp
      (MonoidHom.toHomUnits (CFSG.RankThree.FFModules.autRep W))
  have hρinj : Function.Injective ρ := by
    intro φ ψ h
    have h1 := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive W)).injective h
    exact CFSG.RankThree.FFModules.autRep_injective
      (by simpa only [MonoidHom.coe_toHomUnits] using congrArg Units.val h1)
  have hMW : Nat.card (MulAut W) ∣ Nat.card (Additive W ≃ₗ[ZMod 2] Additive W) :=
    Subgroup.card_dvd_of_injective ρ hρinj
  have hnot : ¬ 3 ^ 6 ∣ Nat.card (Additive W ≃ₗ[ZMod 2] Additive W) := by
    rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod (V := Additive W) hfr]
    exact w107_not_dvd_prod_two_pow (rk W) hrk
  exact hnot (dvd_trans (dvd_trans hdiv hH) hMW)

theorem w107_false_of_rk_le_six {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (h : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1)
    (hrk : rk W ≤ 6) : False :=
  w107_not_three_pow_six_dvd_card_of_rk_le_six hW hrk L (w107_three_pow_six_dvd h)

end CFSG.LocalAnalysis.WeakClosure81
