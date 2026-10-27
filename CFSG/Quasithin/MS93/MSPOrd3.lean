module

public import CFSG.Quasithin.MS93.MSPHeis

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

theorem transv_mul_transv_mulVec (u v : V4 F) (a b : F) (x : V4 F) :
    mat (transv u a * transv v b) *ᵥ x =
      x + (b * form F v x) • v + (a * (form F u x + b * form F v x * form F u v)) • u := by
  rw [mat_mul_mulVec, transv_mulVec, transv_mulVec, map_add, map_smul, smul_eq_mul]

theorem transv_mul_transv_mulVec_of_form {u v w : V4 F} (hu : form F u w = 0)
    (hv : form F v w = 0) (a b : F) : mat (transv u a * transv v b) *ᵥ w = w := by
  rw [transv_mul_transv_mulVec, hu, hv]
  simp

theorem transv_mul_transv_mulVec_right (u v : V4 F) (a b : F) :
    mat (transv u a * transv v b) *ᵥ v = v + (a * form F u v) • u := by
  rw [transv_mul_transv_mulVec, form_self]
  simp

theorem exists_form_eq_one_of_perp_e₁ {y : V4 F} (hy : y (.inl 1) ≠ 0 ∨ y (.inr 1) ≠ 0) :
    ∃ v : V4 F, v (.inr 0) = 0 ∧ form F y v = 1 := by
  rcases hy with hy | hy
  · refine ⟨(y (.inl 1))⁻¹ • f₂ F, by simp, ?_⟩
    rw [map_smul, form_swap, form_f₂, smul_eq_mul, neg_neg, inv_mul_cancel₀ hy]
  · refine ⟨(-y (.inr 1))⁻¹ • e₂ F, by simp, ?_⟩
    rw [map_smul, form_swap, form_e₂, smul_eq_mul, inv_mul_cancel₀ (neg_ne_zero.2 hy)]

section CharTwo

variable [CharP F 2]

theorem transv_mul_transv_mulVec_left {u v : V4 F} (huv : form F u v = 1) {a b : F}
    (hab : a * b = 1) : mat (transv u a * transv v b) *ᵥ u = b • v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [transv_mul_transv_mulVec, form_self, form_swap u v, huv]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(u i)) * hab - (b * v i) * h2

theorem transv_mul_transv_pow_three {u v : V4 F} (huv : form F u v = 1) {a b : F}
    (hab : a * b = 1) : (transv u a * transv v b) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set g := transv u a * transv v b with hg
  have hvu : form F v u = -1 := by rw [form_swap, huv]
  have hgx : ∀ x, mat g *ᵥ x =
      x + (b * form F v x) • v + (a * (form F u x + b * form F v x)) • u :=
    fun x => by rw [hg, transv_mul_transv_mulVec, huv, mul_one]
  have hfv : ∀ x, form F v (mat g *ᵥ x) = -(a * form F u x) := fun x => by
    rw [hgx]
    simp only [map_add, map_smul, smul_eq_mul, form_self, hvu]
    linear_combination (-(form F v x)) * hab
  have hfu : ∀ x, form F u (mat g *ᵥ x) = form F u x + b * form F v x := fun x => by
    rw [hgx]
    simp only [map_add, map_smul, smul_eq_mul, form_self, huv]
    ring
  refine ext_mulVec fun x => ?_
  rw [pow_succ, pow_succ, pow_one, mat_mul_mulVec, mat_mul_mulVec, mat_one, one_mulVec]
  obtain ⟨p, hp⟩ : ∃ p, p = form F v x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = form F u x := ⟨_, rfl⟩
  have h₁ : mat g *ᵥ x = x + (b * p) • v + (a * (r + b * p)) • u := by rw [hgx, hp, hr]
  have hp₁ : form F v (mat g *ᵥ x) = -(a * r) := by rw [hfv, hr]
  have hr₁ : form F u (mat g *ᵥ x) = r + b * p := by rw [hfu, hp, hr]
  have h₂ : mat g *ᵥ (mat g *ᵥ x) = mat g *ᵥ x + (b * -(a * r)) • v +
      (a * (r + b * p + b * -(a * r))) • u := by
    rw [hgx (mat g *ᵥ x), hp₁, hr₁]
  have hp₂ : form F v (mat g *ᵥ (mat g *ᵥ x)) = -(a * (r + b * p)) := by rw [hfv, hr₁]
  have hr₂ : form F u (mat g *ᵥ (mat g *ᵥ x)) = r + b * p + b * -(a * r) := by
    rw [hfu, hr₁, hp₁]
  have h₃ : mat g *ᵥ (mat g *ᵥ (mat g *ᵥ x)) = mat g *ᵥ (mat g *ᵥ x) +
      (b * -(a * (r + b * p))) • v +
      (a * (r + b * p + b * -(a * r) + b * -(a * (r + b * p)))) • u := by
    rw [hgx (mat g *ᵥ (mat g *ᵥ x)), hp₂, hr₂]
  rw [h₃, h₂, h₁]
  have hc₁ : b * p + b * -(a * r) + b * -(a * (r + b * p)) = 0 := by
    linear_combination (-b * p - 2 * r) * hab - r * h2
  have hc₂ : a * (r + b * p) + a * (r + b * p + b * -(a * r)) +
      a * (r + b * p + b * -(a * r) + b * -(a * (r + b * p))) = 0 := by
    linear_combination (-3 * a * r - p * (a * b - 2)) * hab + p * h2
  calc _ = x + (b * p + b * -(a * r) + b * -(a * (r + b * p))) • v +
        (a * (r + b * p) + a * (r + b * p + b * -(a * r)) +
          a * (r + b * p + b * -(a * r) + b * -(a * (r + b * p)))) • u := by module
    _ = x := by rw [hc₁, hc₂, zero_smul, zero_smul, add_zero, add_zero]

end CharTwo

end CFSG.Quasithin.MS93.MSP
