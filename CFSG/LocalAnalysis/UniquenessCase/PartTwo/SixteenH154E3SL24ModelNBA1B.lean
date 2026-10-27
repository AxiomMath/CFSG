module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBA1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13
open scoped Matrix

theorem s16h_gf4_sq_sq : ∀ x : GF4, (x ^ 2) ^ 2 = x := by
  decide +kernel

theorem s16h_gf4_add_sq : ∀ x y : GF4, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  decide +kernel

theorem s16h_gf4_exists_sq : ∀ δ : GF4, δ ≠ 0 → ∃ μ : GF4, μ ≠ 0 ∧ μ ^ 2 = δ := by
  decide +kernel

@[expose] def s16h_frobW : (Fin 2 → GF4) ≃+ (Fin 2 → GF4) where
  toFun w := fun i => w i ^ 2
  invFun w := fun i => w i ^ 2
  left_inv w := by
    funext i
    exact s16h_gf4_sq_sq (w i)
  right_inv w := by
    funext i
    exact s16h_gf4_sq_sq (w i)
  map_add' w w' := by
    funext i
    exact s16h_gf4_add_sq (w i) (w' i)

theorem s16h_linear_form (g : (Fin 2 → GF4) ≃+ (Fin 2 → GF4))
    (hlin : ∀ (a : GF4) (w : Fin 2 → GF4), g (a • w) = a • g w) :
    ∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ w : Fin 2 → GF4,
      g w = μ • ((((γ : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4)).mulVec w) := by
  let M : Matrix (Fin 2) (Fin 2) GF4 := fun i j => g (Pi.single j 1) i
  have hM : ∀ w : Fin 2 → GF4, g w = M.mulVec w := by
    intro w
    have hdecomp : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
      funext i
      fin_cases i <;> simp
    nth_rewrite 1 [hdecomp]
    rw [map_add, hlin, hlin]
    funext i
    fin_cases i <;>
      simp [M, Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, mul_comm]
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have h : g a = g b := by rw [hM a, hM b, hab]
    exact g.injective h
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : M.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hunit)
  obtain ⟨μ, hμ, hμ2⟩ := s16h_gf4_exists_sq M.det hdet
  let A : Matrix (Fin 2) (Fin 2) GF4 := μ⁻¹ • M
  have hAdet1 : A.det = 1 := by
    rw [Matrix.det_smul, ← hμ2]
    simp only [Fintype.card_fin]
    rw [← mul_pow, inv_mul_cancel₀ hμ, one_pow]
  let γsl : Matrix.SpecialLinearGroup (Fin 2) GF4 := ⟨A, hAdet1⟩
  refine ⟨μ, hμ, ⟨Matrix.SpecialLinearGroup.toGL γsl, ?_⟩, fun w => ?_⟩
  · rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
    exact ⟨γsl, rfl⟩
  · rw [hM w]
    show M.mulVec w = μ • ((((Matrix.SpecialLinearGroup.toGL γsl : GL (Fin 2) GF4)) :
      Matrix (Fin 2) (Fin 2) GF4)).mulVec w
    rw [show (((Matrix.SpecialLinearGroup.toGL γsl : GL (Fin 2) GF4)) :
      Matrix (Fin 2) (Fin 2) GF4) = A from rfl]
    rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hμ, one_smul]

theorem s16h_sl2_normalizer_add_form (g : (Fin 2 → GF4) ≃+ (Fin 2 → GF4))
    (hg : NormalizesSL2 g) :
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ w : Fin 2 → GF4,
      g w = μ • ((((γ : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4)).mulVec w)) ∨
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ w : Fin 2 → GF4,
      g w = μ • ((((γ : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4)).mulVec (s16h_frobW w))) := by
  obtain ⟨σ, hσ⟩ := NormalizesSL2.exists_semilinear hg
  rcases s16h_gf4_ringAut_eq σ with hid | hfrob
  · left
    exact s16h_linear_form g fun a w => by rw [hσ, hid]
  · right
    let h : (Fin 2 → GF4) ≃+ (Fin 2 → GF4) := s16h_frobW.symm.trans g
    have hlin : ∀ (a : GF4) (w : Fin 2 → GF4), h (a • w) = a • h w := by
      intro a w
      have hPhi : s16h_frobW (a • w) = a ^ 2 • s16h_frobW w := by
        funext i
        simp [s16h_frobW, Pi.smul_apply, mul_pow]
      show g (s16h_frobW (a • w)) = a • g (s16h_frobW w)
      rw [hPhi, hσ, hfrob (a ^ 2), s16h_gf4_sq_sq a]
    obtain ⟨μ, hμ, γ, hform⟩ := s16h_linear_form h hlin
    refine ⟨μ, hμ, γ, fun w => ?_⟩
    have hgw : g w = h (s16h_frobW w) := by
      show g w = (s16h_frobW.symm.trans g) (s16h_frobW w)
      rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [hgw, hform]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
