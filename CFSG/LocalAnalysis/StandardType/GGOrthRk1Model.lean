module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Omega
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Prod

public section

open Module

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D]

noncomputable def rk1MatAct (M : Matrix (Fin 2) (Fin 2) K) : (D × D) →ₗ[K] (D × D) :=
  (M 0 0 • LinearMap.fst K D D + M 0 1 • LinearMap.snd K D D).prod
    (M 1 0 • LinearMap.fst K D D + M 1 1 • LinearMap.snd K D D)

theorem rk1MatAct_apply (M : Matrix (Fin 2) (Fin 2) K) (v : D × D) :
    rk1MatAct M v = (M 0 0 • v.1 + M 0 1 • v.2, M 1 0 • v.1 + M 1 1 • v.2) := by
  simp [rk1MatAct]

theorem rk1MatAct_mul (M N : Matrix (Fin 2) (Fin 2) K) :
    rk1MatAct (D := D) (M * N) = rk1MatAct M ∘ₗ rk1MatAct N := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, rk1MatAct_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Prod.mk.injEq]
  constructor <;> module

theorem rk1MatAct_one : rk1MatAct (D := D) (1 : Matrix (Fin 2) (Fin 2) K) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp [rk1MatAct_apply]

noncomputable def rk1ModelAct :
    Matrix.SpecialLinearGroup (Fin 2) K →* ((D × D) ≃ₗ[K] (D × D)) where
  toFun g := LinearEquiv.ofLinear (rk1MatAct (g : Matrix (Fin 2) (Fin 2) K))
    (rk1MatAct ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (by
      rw [← rk1MatAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, rk1MatAct_one])
    (by
      rw [← rk1MatAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, rk1MatAct_one])
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change rk1MatAct ((1 : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) v = v
    rw [Matrix.SpecialLinearGroup.coe_one, rk1MatAct_one]
    rfl
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply]
    change rk1MatAct ((g * h : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) v = rk1MatAct (g : Matrix (Fin 2) (Fin 2) K)
          (rk1MatAct (h : Matrix (Fin 2) (Fin 2) K) v)
    rw [Matrix.SpecialLinearGroup.coe_mul, rk1MatAct_mul, LinearMap.comp_apply]

theorem rk1ModelAct_apply (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : D × D) :
    rk1ModelAct g v = (g 0 0 • v.1 + g 0 1 • v.2, g 1 0 • v.1 + g 1 1 • v.2) := by
  change rk1MatAct (g : Matrix (Fin 2) (Fin 2) K) v =
    (g 0 0 • v.1 + g 0 1 • v.2, g 1 0 • v.1 + g 1 1 • v.2)
  rw [rk1MatAct_apply]

theorem rk1ModelAct_injective [Nontrivial D] :
    Function.Injective (rk1ModelAct (K := K) (D := D)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨d, hd⟩ := exists_ne (0 : D)
  have h0 : rk1ModelAct g (d, 0) = (d, 0) := by rw [hg]; rfl
  rw [rk1ModelAct_apply] at h0
  have h1 : rk1ModelAct g (0, d) = (0, d) := by rw [hg]; rfl
  rw [rk1ModelAct_apply] at h1
  have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    apply smul_left_injective K hd
    simpa using (Prod.ext_iff.mp h0).1
  have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    apply smul_left_injective K hd
    simpa using (Prod.ext_iff.mp h0).2
  have h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    apply smul_left_injective K hd
    simpa using (Prod.ext_iff.mp h1).1
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    apply smul_left_injective K hd
    simpa using (Prod.ext_iff.mp h1).2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h01, h10, h11, Matrix.SpecialLinearGroup.coe_one]

theorem rk1ModelAct_map (g : Matrix.SpecialLinearGroup (Fin 2) K) (e : D →ₗ[K] D) (v : D × D) :
    rk1ModelAct g (e v.1, e v.2) = (e (rk1ModelAct g v).1, e (rk1ModelAct g v).2) := by
  simp only [rk1ModelAct_apply, map_add, map_smul]

theorem rk1ModelAct_omega [FiniteDimensional K D] (hD : finrank K D = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : D × D) :
    rk1Omega hD (rk1ModelAct g v).1 (rk1ModelAct g v).2 = rk1Omega hD v.1 v.2 := by
  have hxx : rk1Omega hD v.1 v.1 = 0 := rk1Omega_self hD v.1
  have hyy : rk1Omega hD v.2 v.2 = 0 := rk1Omega_self hD v.2
  have hyx : rk1Omega hD v.2 v.1 = - rk1Omega hD v.1 v.2 := by
    have h := rk1Omega_self hD (v.1 + v.2)
    rw [LinearMap.map_add₂, map_add, map_add, hxx, hyy, add_zero, zero_add] at h
    exact eq_neg_of_add_eq_zero_right h
  have hB : rk1Omega hD (g 0 0 • v.1 + g 0 1 • v.2) (g 1 0 • v.1 + g 1 1 • v.2) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * rk1Omega hD v.1 v.2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxx, hyy, hyx]
    ring
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  rw [rk1ModelAct_apply]
  dsimp only
  rw [hB, hdet, one_mul]

end OrthTorus

end CFSG.StandardType

end
