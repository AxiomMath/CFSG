module

public import CFSG.Quasithin.Vol2.Ch10SecC3I
public import CFSG.Quasithin.Vol2.Ch10SecC3H

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut)
open scoped Matrix

variable {K : Type} [Field K]

theorem addMap_sc_mul_fa (y : Kˣ) (σ : K ≃+* K) (i j : Fin 2) (c : K) :
    addMap (sc y * fa σ) (Matrix.single i j c) = Matrix.single i j (σ c * y) := by
  rw [addMap_apply, MulAut.mul_apply, toAdd_sc, toAdd_fa, toAdd_ofAdd]
  ext a b
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem eq_sc_mul_fa [CharP K 2] {ψ : MulAut (WM K)} {σ₁ σ₂ : K ≃+* K}
    (h : ∀ g : SL K × SL K,
      ψ * rho K g = rho K (slFieldAut K σ₁ g.1, slFieldAut K σ₂ g.2) * ψ) :
    σ₁ = σ₂ ∧ ∃ y : Kˣ, ψ = sc y * fa σ₁ := by
  have hψ : ∀ (g : SL K × SL K) (X : WM K),
      ψ (rho K g X) = rho K (slFieldAut K σ₁ g.1, slFieldAut K σ₂ g.2) (ψ X) := fun g X => by
    have := congrArg (fun φ : MulAut (WM K) => φ X) (h g)
    simpa only [MulAut.mul_apply] using this
  set E : WM K := Multiplicative.ofAdd (Matrix.single 0 0 1) with hE
  set Y := Multiplicative.toAdd (ψ E) with hYdef
  have hY1 : ((u : SL K) : Matrix (Fin 2) (Fin 2) K) * Y = Y := by
    have h1 := hψ (u, 1) E
    rw [rho_u_one_single, slFieldAut_u, map_one] at h1
    have h2 := congrArg Multiplicative.toAdd h1.symm
    rw [toAdd_rho] at h2
    simpa using h2
  have hY2 : Y * ((u : SL K) : Matrix (Fin 2) (Fin 2) K)ᵀ = Y := by
    have h1 := hψ (1, u) E
    rw [rho_one_u_single, slFieldAut_u, map_one] at h1
    have h2 := congrArg Multiplicative.toAdd h1.symm
    rw [toAdd_rho] at h2
    simpa using h2
  have hYs : Y = Matrix.single 0 0 (Y 0 0) := eq_single_of_fix hY1 hY2
  set y₀ := Y 0 0 with hy₀def
  have hy₀ : y₀ ≠ 0 := by
    intro h0
    rw [h0, Matrix.single_zero] at hYs
    have hψ1 : ψ E = ψ 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      rw [← hYdef, hYs]
      rfl
    have h3 := congrArg Multiplicative.toAdd (ψ.injective hψ1)
    have h4 := congrFun (congrFun h3 0) 0
    simp [hE] at h4
  have hψE : ψ E = Multiplicative.ofAdd (Matrix.single 0 0 y₀) := by
    apply Multiplicative.toAdd.injective
    rw [← hYdef, ← hYs]
    rfl
  have hc1 : ∀ t : Kˣ, addMap ψ (Matrix.single 0 0 (t : K)) =
      Matrix.single 0 0 (σ₁ t * y₀) := by
    intro t
    have h1 := hψ (d t, 1) E
    rw [rho_d_one_single, mul_one, slFieldAut_d, map_one, hψE, rho_d_one_single] at h1
    rw [addMap_apply, h1]
    rfl
  have hc2 : ∀ t : Kˣ, addMap ψ (Matrix.single 0 0 (t : K)) =
      Matrix.single 0 0 (σ₂ t * y₀) := by
    intro t
    have h1 := hψ (1, d t) E
    rw [rho_one_d_single, mul_one, slFieldAut_d, map_one, hψE, rho_one_d_single] at h1
    rw [addMap_apply, h1]
    rfl
  have hσ : σ₁ = σ₂ := by
    refine RingEquiv.ext fun c => ?_
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero]
    have h3 := (hc1 (Units.mk0 c hc)).symm.trans (hc2 (Units.mk0 c hc))
    have h4 := congrFun (congrFun h3 0) 0
    simp only [Matrix.single_apply_same, Units.val_mk0] at h4
    exact mul_right_cancel₀ hy₀ h4
  refine ⟨hσ, Units.mk0 y₀ hy₀, ?_⟩
  have hc00 : ∀ c : K, addMap ψ (Matrix.single 0 0 c) = Matrix.single 0 0 (σ₁ c * y₀) := by
    intro c
    by_cases hc : c = 0
    · rw [hc, Matrix.single_zero, map_zero, map_zero, zero_mul, Matrix.single_zero]
    · exact hc1 (Units.mk0 c hc)
  have hcij : ∀ (i j : Fin 2) (c : K),
      addMap ψ (Matrix.single i j c) = Matrix.single i j (σ₁ c * y₀) := by
    intro i j c
    have h1 := hψ (sel i, sel j) (Multiplicative.ofAdd (Matrix.single 0 0 c))
    rw [rho_sel_single, slFieldAut_sel, slFieldAut_sel] at h1
    rw [addMap_apply, h1]
    have h2 : ψ (Multiplicative.ofAdd (Matrix.single 0 0 c)) =
        Multiplicative.ofAdd (Matrix.single 0 0 (σ₁ c * y₀)) := by
      apply Multiplicative.toAdd.injective
      exact hc00 c
    rw [h2, rho_sel_single]
    rfl
  have hext : ∀ X : Matrix (Fin 2) (Fin 2) K,
      addMap ψ X = addMap (sc (Units.mk0 y₀ hy₀) * fa σ₁) X := by
    intro X
    rw [Matrix.matrix_eq_sum_single X, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcij, addMap_sc_mul_fa, Units.val_mk0]
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  exact hext (Multiplicative.toAdd X)

end CFSG.Quasithin.Vol2.Ch10.C3.Om
