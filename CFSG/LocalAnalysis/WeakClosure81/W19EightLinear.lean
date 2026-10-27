module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_eq_zero_of_zmod_two (v : W) : v + v = 0 := by
  have h : ((1 : ZMod 2) + 1) = 0 := by decide
  calc v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [h, zero_smul]

theorem nsmul_eq_self_of_odd {n : ℕ} (hn : Odd n) (v : W) : n • v = v := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => simp
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    rw [e, add_nsmul, ih, two_nsmul, add_self_eq_zero_of_zmod_two, add_zero]

theorem sub_eq_zero_of_fix {x : LGL 2 W} (hodd : Odd (orderOf x)) {u : W}
    (h : x (x u - u) = x u - u) : x u - u = 0 := by
  have key : ∀ k : ℕ, (x ^ k) u = u + k • (x u - u) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, h, succ_nsmul]
      abel
  have h1 := key (orderOf x)
  rw [pow_orderOf_eq_one] at h1
  have h2 : u = u + (orderOf x) • (x u - u) := h1
  rw [nsmul_eq_self_of_odd hodd] at h2
  exact (add_left_cancel (a := u) (by rw [add_zero]; exact h2)).symm

theorem fix_of_sq_fix {x : LGL 2 W} (hodd : Odd (orderOf x)) {v : W} (h : x (x v) = v) :
    x v = v := by
  obtain ⟨m, hm⟩ := hodd
  have key : ∀ k : ℕ, (x ^ (2 * k)) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : x ^ (2 * (k + 1)) = x ^ (2 * k) * (x * x) := by
        rw [mul_add, mul_one, pow_add, pow_two]
      rw [e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h, ih]
  have e : x ^ (2 * (m + 1)) = x := by
    have : 2 * (m + 1) = orderOf x + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have := key (m + 1)
  rwa [e] at this

theorem eq_one_of_dihedral_fix {a x : LGL 2 W} (ha : a * a = 1) (hax : a * x * a⁻¹ = x⁻¹)
    (hodd : Odd (orderOf x)) (hfix : ∀ u : W, a (x u - u) = x u - u) : x = 1 := by
  have hax' : a * x = x⁻¹ * a := by
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x⁻¹ * a := by rw [hax]
  have hax'' : ∀ u : W, a (x u) = x⁻¹ (a u) := fun u => by
    have := congrArg (fun f : LGL 2 W => f u) hax'
    simpa [LinearEquiv.mul_apply] using this
  have haa : ∀ u : W, a (a u) = u := fun u => by
    have := congrArg (fun f : LGL 2 W => f u) ha
    simpa [LinearEquiv.mul_apply] using this
  have hstar : ∀ u : W, x⁻¹ (a u) - a u = x u - u := fun u => by
    have := hfix u
    rwa [map_sub, hax''] at this
  have hNa : ∀ v : W, x (a v) - a v = x⁻¹ v - v := fun v => by
    have := hstar (a v)
    rw [haa] at this
    exact this.symm
  have hxv : ∀ u : W, x (x u - u) = x u - u := by
    intro u
    have h1 : a (x u - u) = x u - u := hfix u
    have h2 := hNa (x u - u)
    rw [h1] at h2
    have h3 : x (x u - u) = x⁻¹ (x u - u) := sub_left_injective h2
    refine fix_of_sq_fix hodd ?_
    rw [h3]
    exact LinearEquiv.apply_symm_apply x _
  refine LinearEquiv.ext fun u => ?_
  have := sub_eq_zero.1 (sub_eq_zero_of_fix hodd (hxv u))
  simpa using this

end CFSG.LocalAnalysis.WeakClosure81

end
