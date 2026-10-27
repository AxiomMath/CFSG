module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Model
public import CFSG.Milestones.ASVolI.I2Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup CFSG.ASVolI

open scoped Matrix

instance s16h_charP_GF4 : CharP GF4 2 :=
  CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (K := GF4) (n := 2) (by norm_num)
    (by rw [Nat.card_eq_fintype_card]; decide)

@[expose] def s16h_sl24_coordAddEquiv : ((Fin 2 → GF4) × GF4) ≃+ (GF4 × GF4 × GF4) where
  toFun w := (w.1 0, w.1 1, w.2)
  invFun v := (![v.1, v.2.1], v.2.2)
  left_inv w := by
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv v := by
    ext <;> simp
  map_add' a b := by
    ext <;> simp

@[expose] def s16h_sl24_coordEquiv :
    Multiplicative ((Fin 2 → GF4) × GF4) ≃* Orth3 :=
  s16h_sl24_coordAddEquiv.toMultiplicative

@[simp] theorem s16h_sl24_coordEquiv_apply (w : (Fin 2 → GF4) × GF4) :
    s16h_sl24_coordEquiv (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd (w.1 0, w.1 1, w.2) := rfl

theorem s16h_sl24_sqrt_eq_sq (t : GF4) : burnsideI23x_sqrt GF4 t = t ^ 2 := by
  apply burnsideI23x_sq_injective
  rw [burnsideI23x_sqrt_sq]
  have h : (t ^ 2) ^ 2 = t := by revert t; decide
  exact h.symm

theorem s16h_sl24_lf_key (a b c d x0 x1 : GF4) (h : a * d + b * c = 1) :
    (x0 * x1 + (a * x0 + b * x1) * (c * x0 + d * x1)) ^ 2 =
      (a * c) ^ 2 * x0 + (b * d) ^ 2 * x1 := by
  revert a b c d x0 x1
  decide +kernel

theorem s16h_sl24_det_add (M : Matrix (Fin 2) (Fin 2) GF4) (h : M.det = 1) :
    M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
  rw [Matrix.det_fin_two] at h
  have h2 : (2 : GF4) = 0 := CharP.cast_eq_zero GF4 2
  linear_combination h + (M 0 1 * M 1 0) * h2

theorem s16h_sl24_liftHom_orth3
    (A : ↥(StatedSL 2 GF4) →* ((Fin 2 → GF4) ≃ₗ[GF4] (Fin 2 → GF4)))
    (hA : ∀ γ, (burnsideI23x_sd1 GF4).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM1 GF4).lin γ x)
    (γ : ↥(StatedSL 2 GF4)) (v : Multiplicative ((Fin 2 → GF4) × GF4)) :
    s16h_sl24_coordEquiv ((burnsideI23x_sd1 GF4).liftHom A hA γ v) =
      Multiplicative.ofAdd (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4)
        (Multiplicative.toAdd (s16h_sl24_coordEquiv v))) := by
  set w : (Fin 2 → GF4) × GF4 := Multiplicative.toAdd v with hw
  have hv : v = Multiplicative.ofAdd w := by rw [hw, ofAdd_toAdd]
  set M : Matrix (Fin 2) (Fin 2) GF4 :=
    ((γ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4) with hM
  have hmv : A γ w.1 = M.mulVec w.1 := by
    rw [hAlin γ w.1]
    exact CFSG.Quasithin.Vol2.KGNat.linModelNat_lin (StatedSL 2 GF4) γ w.1
  have hdet : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 :=
    s16h_sl24_det_add M (by
      rw [hM]
      exact CFSG.Open.StatedAPI.det_of_mem_statedSL γ.2)
  have h0 : (A γ w.1) 0 = M 0 0 * w.1 0 + M 0 1 * w.1 1 := by
    rw [hmv]
    simp [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_two]
  have h1 : (A γ w.1) 1 = M 1 0 * w.1 0 + M 1 1 * w.1 1 := by
    rw [hmv]
    simp [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_two]
  have hlf : (burnsideI23x_sd1 GF4).lf (A γ) w.1 =
      (M 0 0 * M 1 0) ^ 2 * w.1 0 + (M 0 1 * M 1 1) ^ 2 * w.1 1 := by
    rw [burnsideI23x_SD.lf, s16h_sl24_sqrt_eq_sq, burnsideI23x_sd1_Q0, burnsideI23x_sd1_Q0,
      h0, h1]
    exact s16h_sl24_lf_key (M 0 0) (M 0 1) (M 1 0) (M 1 1) (w.1 0) (w.1 1) hdet
  rw [hv, burnsideI23x_SD.liftHom_apply, burnsideI23x_SD.lift_apply,
    s16h_sl24_coordEquiv_apply, s16h_sl24_coordEquiv_apply]
  apply congrArg Multiplicative.ofAdd
  dsimp only
  rw [toAdd_ofAdd, h0, h1, hlf, orth3Act]
  ext <;> ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
