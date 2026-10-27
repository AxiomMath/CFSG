module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_sq_eq_neg {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) (hg : g ^ 3 = 1) (W : Submodule F V) (hW : ∀ w ∈ W, g w ∈ W)
    (hg1 : ∀ w ∈ W, g w = w → w = 0) {w : V} (hw : w ∈ W) :
    g (g w) = -(g w) - w := by
  have hgw : g w ∈ W := hW w hw
  have hggw : g (g w) ∈ W := hW (g w) hgw
  have hu : g (g w) + g w + w ∈ W := W.add_mem (W.add_mem hggw hgw) hw
  have h3 : g (g (g w)) = w := by
    have hg' : g * g * g = 1 := by rw [← pow_three']; exact hg
    simpa using congrArg (fun f : V ≃ₗ[F] V => f w) hg'
  have hsum : g (g w) + g w + w = 0 := by
    refine hg1 _ hu ?_
    simp only [LinearEquiv.map_add, h3]
    module
  have h : g (g w) + (g w + w) = 0 := by
    simpa only [← add_assoc] using hsum
  rw [add_eq_zero_iff_eq_neg, neg_add] at h
  simpa only [sub_eq_add_neg] using h

private lemma k330c_map_neg {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (f : V ≃ₗ[F] V) (a : V) : f (-a) = -f a := by
  have h : f (-a) + f a = 0 := by
    rw [← LinearEquiv.map_add f (-a) a, neg_add_cancel, LinearEquiv.map_zero f]
  exact eq_neg_of_add_eq_zero_left h

private lemma k330c_map_sub {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (f : V ≃ₗ[F] V) (a b : V) : f (a - b) = f a - f b := by
  simp only [sub_eq_add_neg, LinearEquiv.map_add, k330c_map_neg]

theorem e9_fpf {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (h3 : (3 : F) ≠ 0) (x y : V ≃ₗ[F] V) (hxy : x * y = y * x) (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (W : Submodule F V) (hWx : ∀ w ∈ W, x w ∈ W) (hWy : ∀ w ∈ W, y w ∈ W)
    (hx1 : ∀ w ∈ W, x w = w → w = 0) (hy1 : ∀ w ∈ W, y w = w → w = 0)
    (hxy1 : ∀ w ∈ W, (x * y) w = w → w = 0) (hxy2 : ∀ w ∈ W, (x * y ^ 2) w = w → w = 0) :
    W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hcomm : Commute x y := hxy
  have hx2 : x (x w) = -x w - w := k330c_sq_eq_neg x hx W hWx hx1 hw
  have hy2 : y (y w) = -y w - w := k330c_sq_eq_neg y hy W hWy hy1 hw
  have hxyw : x (x (y w)) = -x (y w) - y w :=
    k330c_sq_eq_neg x hx W hWx hx1 (hWy w hw)
  have hxyc : (x * y) ^ 3 = 1 := by
    rw [hcomm.mul_pow 3, hx, hy, one_mul]
  have hxy2c : (x * y ^ 2) ^ 3 = 1 := by
    have hy6 : y ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hy, one_pow]
    rw [(hcomm.pow_right 2).mul_pow 3, hx, one_mul, ← pow_mul,
      show (2 * 3 : ℕ) = 6 from rfl, hy6]
  have hXyW : ∀ z ∈ W, (x * y) z ∈ W := by
    intro z hz
    rw [LinearEquiv.mul_apply]
    exact hWx (y z) (hWy z hz)
  have hXy2W : ∀ z ∈ W, (x * y ^ 2) z ∈ W := by
    intro z hz
    rw [LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply]
    exact hWx (y (y z)) (hWy (y z) (hWy z hz))
  have hXYsq : (x * y) ((x * y) w) = x w + y w + x (y w) + w := by
    have h1 : (x * y) ((x * y) w) = (x ^ 2 * y ^ 2) w := by
      rw [← LinearEquiv.mul_apply, ← pow_two, hcomm.mul_pow 2]
    rw [h1, LinearEquiv.mul_apply]
    rw [show (y ^ 2) w = y (y w) by rw [pow_two, LinearEquiv.mul_apply]]
    rw [hy2]
    simp only [pow_two, LinearEquiv.mul_apply, k330c_map_sub, k330c_map_neg]
    rw [hxyw, hx2]
    module
  have hXY2sq : (x * y ^ 2) ((x * y ^ 2) w) = -x (y w) - y w := by
    have hy4 : y ^ 4 = y := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hy, pow_one, one_mul]
    have h1 : (x * y ^ 2) ((x * y ^ 2) w) = (x ^ 2 * y) w := by
      rw [← LinearEquiv.mul_apply, ← pow_two, (hcomm.pow_right 2).mul_pow 2,
        ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, hy4]
    rw [h1, LinearEquiv.mul_apply]
    simp only [pow_two, LinearEquiv.mul_apply]
    rw [hxyw]
  have hxy2w : (x * y ^ 2) w = -x (y w) - x w := by
    rw [LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply, hy2]
    simp only [k330c_map_sub, k330c_map_neg]
  have hsum1 : (x * y) ((x * y) w) + (x * y) w + w = 0 := by
    have hrel := k330c_sq_eq_neg (x * y) hxyc W hXyW hxy1 hw
    rw [hrel]; module
  rw [hXYsq, LinearEquiv.mul_apply] at hsum1
  have hsum2 : (x * y ^ 2) ((x * y ^ 2) w) + (x * y ^ 2) w + w = 0 := by
    have hrel := k330c_sq_eq_neg (x * y ^ 2) hxy2c W hXy2W hxy2 hw
    rw [hrel]; module
  rw [hXY2sq, hxy2w] at hsum2
  have h3w : (3 : F) • w = 0 := by
    have hAB : (3 : F) • w =
        ((x w + y w + x (y w) + w) + x (y w) + w)
          + ((-x (y w) - y w) + (-x (y w) - x w) + w) := by
      module
    rw [hAB]
    rw [hsum1, hsum2, add_zero]
  have hw0 : w = 0 := by
    have hw' : w = (3 : F)⁻¹ • ((3 : F) • w) := by
      rw [smul_smul, inv_mul_cancel₀ h3, one_smul]
    rw [hw', h3w, smul_zero]
  exact hw0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
