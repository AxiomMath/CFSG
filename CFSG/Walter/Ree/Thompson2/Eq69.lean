module

public import CFSG.Walter.Ree.Thompson3.Presentation

public section

namespace CFSG.Walter.Ree.T2

theorem pglK_mul_pglT_pow_three : (pglK * pglT) ^ 3 = 1 := by decide

variable {k : Type} [Field k] [CharP k 3]

theorem torus_inv_mul_pp0_mul_torus (σ : k ≃+* k) (s : kˣ) (y : k) :
    (ThompsonN.torus σ s)⁻¹ * pp σ 0 y 0 * ThompsonN.torus σ s = pp σ 0 (y * (s * σ s)) 0 := by
  simp only [pp, ThompsonN.torus_conj, zero_mul]

namespace RType

variable {G : Type} [Group G] [Finite G] {σ : k ≃+* k} {d : k} (R : RType G k σ d)

theorem ι_pp0_inv (y : k) : (R.ι (pp σ 0 y 0))⁻¹ = R.ι (pp σ 0 (-y) 0) := by
  rw [← map_inv]
  congr 1
  simp [pp, ThompsonN.inv_P]

theorem ι_torus_conj_pp0 (s : kˣ) (y : k) :
    (R.ι (ThompsonN.torus σ s))⁻¹ * R.ι (pp σ 0 y 0) * R.ι (ThompsonN.torus σ s) =
      R.ι (pp σ 0 (y * (s * σ s)) 0) := by
  rw [← map_inv, ← map_mul, ← map_mul, torus_inv_mul_pp0_mul_torus]

theorem ι_torus_conj_pp0' (s : kˣ) (y : k) :
    R.ι (ThompsonN.torus σ s) * R.ι (pp σ 0 y 0) * (R.ι (ThompsonN.torus σ s))⁻¹ =
      R.ι (pp σ 0 (y * (s * σ s)⁻¹) 0) := by
  have h := R.ι_torus_conj_pp0 s⁻¹ y
  simp only [map_inv, inv_inv, Units.val_inv_eq_inv_val, map_inv₀] at h
  rw [h, mul_inv]

theorem torus_mul_K_mul_torus (s : kˣ) :
    R.ι (ThompsonN.torus σ s) * R.K * R.ι (ThompsonN.torus σ s) = R.K := by
  rw [mul_assoc, R.K_mul_torus, map_inv, map_inv, ← mul_assoc, mul_inv_cancel, one_mul]

theorem K_mul_T_pow_three : (R.K * R.ι (tT σ)) ^ 3 = 1 := by
  have h : (PGammaL28.k * PGammaL28.t) ^ 3 = 1 := Subtype.ext pglK_mul_pglT_pow_three
  have := congrArg R.base h
  rwa [map_pow, map_mul, map_one, R.base_k, R.base_t] at this

theorem K_T_K : R.K * R.ι (pp σ 0 1 0) * R.K =
    R.ι (pp σ 0 (-1) 0) * R.K * R.ι (pp σ 0 (-1) 0) := by
  have h := R.K_mul_T_pow_three
  rw [tT, pow_three'] at h
  rw [← R.ι_pp0_inv]
  calc R.K * R.ι (pp σ 0 1 0) * R.K
      = (R.K * R.ι (pp σ 0 1 0) * (R.K * R.ι (pp σ 0 1 0)) * (R.K * R.ι (pp σ 0 1 0))) *
        (R.ι (pp σ 0 1 0))⁻¹ * R.K⁻¹ * (R.ι (pp σ 0 1 0))⁻¹ := by group
    _ = (R.ι (pp σ 0 1 0))⁻¹ * R.K * (R.ι (pp σ 0 1 0))⁻¹ := by rw [h, one_mul, R.K_inv_eq]

theorem eq69_neg_norm (s : kˣ) :
    R.ι (pp σ 0 (-(s * σ s)) 0) * R.ι (ThompsonN.torus σ (s⁻¹ * s⁻¹)) * R.K *
      R.ι (pp σ 0 (-(s * σ s)) 0) = R.K * R.ι (pp σ 0 (s * σ s)⁻¹ 0) * R.K := by
  have c1 := R.ι_torus_conj_pp0 s (-1)
  have c2 := R.ι_torus_conj_pp0' s 1
  have c3 := R.torus_mul_K_mul_torus s
  have c3' := R.torus_mul_K_mul_torus s⁻¹
  have c4 : R.ι (ThompsonN.torus σ (s⁻¹ * s⁻¹)) =
      (R.ι (ThompsonN.torus σ s))⁻¹ * (R.ι (ThompsonN.torus σ s))⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
  rw [neg_one_mul] at c1
  rw [one_mul] at c2
  rw [map_inv, map_inv] at c3'
  rw [← c1, ← c2, c4]
  generalize R.ι (ThompsonN.torus σ s) = t at c3 c3' ⊢
  calc t⁻¹ * R.ι (pp σ 0 (-1) 0) * t * (t⁻¹ * t⁻¹) * R.K * (t⁻¹ * R.ι (pp σ 0 (-1) 0) * t)
      = t⁻¹ * (R.ι (pp σ 0 (-1) 0) * (t⁻¹ * R.K * t⁻¹) * R.ι (pp σ 0 (-1) 0)) * t := by group
    _ = t⁻¹ * (R.K * R.ι (pp σ 0 1 0) * R.K) * t := by rw [c3', ← R.K_T_K]
    _ = t⁻¹ * (t * R.K * t) * R.ι (pp σ 0 1 0) * (t⁻¹ * R.K * t⁻¹) * t := by
        rw [c3, c3']; group
    _ = R.K * (t * R.ι (pp σ 0 1 0) * t⁻¹) * R.K := by group

theorem eq69_norm (s : kˣ) :
    R.ι (pp σ 0 (s * σ s) 0) * R.ι (ThompsonN.torus σ (s⁻¹ * s⁻¹)) * R.K *
      R.ι (pp σ 0 (s * σ s) 0) = R.K * R.ι (pp σ 0 (-(s * σ s)⁻¹) 0) * R.K := by
  have h := congrArg (·⁻¹) (R.eq69_neg_norm s)
  simp only [mul_inv_rev, R.K_inv_eq, R.ι_pp0_inv, neg_neg] at h
  have hc : R.ι (ThompsonN.torus σ (s⁻¹ * s⁻¹)) * R.K =
      R.K * (R.ι (ThompsonN.torus σ (s⁻¹ * s⁻¹)))⁻¹ := by
    rw [R.torus_mul_K, map_inv, map_inv]
  rw [mul_assoc _ _ R.K, hc]
  simpa only [mul_assoc, mul_inv_rev] using h

theorem eq69 : Eq69 R := by
  rintro a ⟨b, rfl⟩ haσ x hx
  set u := Units.mk0 x hx
  have hc : u⁻¹ ^ (b + b) = (u ^ b)⁻¹ * (u ^ b)⁻¹ := by rw [pow_add, inv_pow]
  have hn : ((u ^ b : kˣ) : k) * σ (u ^ b : kˣ) = x ∨
      ((u ^ b : kˣ) : k) * σ (u ^ b : kˣ) = -x := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← haσ x]
    simp only [u, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    ring
  rw [hc]
  rcases hn with h | h
  · have := R.eq69_norm (u ^ b)
    rwa [h] at this
  · have := R.eq69_neg_norm (u ^ b)
    rwa [h, neg_neg, inv_neg] at this

end RType

end CFSG.Walter.Ree.T2
