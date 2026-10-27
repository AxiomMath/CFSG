module

public import CFSG.Walter.Ree.Thompson3.Base

public section

namespace CFSG.Walter.Ree.T2

theorem pgl_rel_d : pglK * (pglY ^ 2 * pglT) * pglK * (pglY ^ 2 * pglT)⁻¹ * pglK =
    pglY * pglJ := by decide

theorem pgl_rel_e : pglK * pglY ^ 4 * pglK * pglJ * (pglY ^ 4)⁻¹ * pglK = pglY ^ 5 * pglJ := by
  decide

variable {k : Type} [Field k] [CharP k 3]

theorem tY_sq_mul_tT (σ : k ≃+* k) (d : k) : tY σ d ^ 2 * tT σ = pp σ (-1) 1 (1 - d) := by
  rw [tY_sq]
  simp only [tT, pp]
  rw [ThompsonN.mul_P]
  ext <;> simp

theorem tY_pow_four (σ : k ≃+* k) (d : k) : tY σ d ^ 4 = pp σ 1 0 (1 + d) := by
  rw [pow_succ, tY_cube]
  simp only [tY, pp]
  rw [ThompsonN.mul_P]
  ext
  · rfl
  · simp
  · simp
  · simp only [map_zero, map_one, zero_mul, mul_zero, add_zero]
    ring

namespace RType

variable {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem K_P0_K : R.K * R.ι (pp σ 0 (-1) 1) * R.K =
    R.ι (tY σ d ^ 2 * ThompsonN.J σ) * R.K * R.ι (pp σ 0 (-1) 1) := by
  have h := R.rel_a
  rw [map_mul, map_pow]
  change R.K * R.ι (pp σ 0 (-1) 1) * R.K = R.ι (tY σ d) ^ 2 * R.Jg * R.K * R.ι (pp σ 0 (-1) 1)
  rw [← h]
  calc R.K * R.ι (pp σ 0 (-1) 1) * R.K = R.K * R.ι (pp σ 0 (-1) 1) * R.K *
        (R.ι (pp σ 0 (-1) 1))⁻¹ * (R.K * R.K) * R.ι (pp σ 0 (-1) 1) := by
          rw [R.K_mul_K]; group
    _ = _ := by group

theorem rel_d : R.K * R.ι (pp σ (-1) 1 (1 - d)) * R.K * (R.ι (pp σ (-1) 1 (1 - d)))⁻¹ * R.K =
    R.ι (tY σ d) * R.Jg := by
  have h := R.base_mul_rel (a := PGammaL28.k * (PGammaL28.y ^ 2 * PGammaL28.t) * PGammaL28.k *
    (PGammaL28.y ^ 2 * PGammaL28.t)⁻¹ * PGammaL28.k) (b := PGammaL28.y * PGammaL28.j)
    (by simpa using pgl_rel_d)
  simp only [map_mul, map_inv, map_pow, R.base_k, R.base_t, R.base_y, R.base_j] at h
  rw [← tY_sq_mul_tT σ d, map_mul, map_pow]
  exact h

theorem K_fixes_Y2T
    [Finite k] : R.act (some (-1, 1, 1 - d)) R.K = some (-1, 1, 1 - d) := by
  apply R.act_K_of_eq (ν := tY σ d * ThompsonN.J σ)
  have h := R.rel_d
  rw [map_mul]
  change R.K * R.ι (pp σ (-1) 1 (1 - d)) * R.K =
    R.ι (tY σ d) * R.Jg * R.K * R.ι (pp σ (-1) 1 (1 - d))
  rw [← h]
  calc R.K * R.ι (pp σ (-1) 1 (1 - d)) * R.K = R.K * R.ι (pp σ (-1) 1 (1 - d)) * R.K *
        (R.ι (pp σ (-1) 1 (1 - d)))⁻¹ * (R.K * R.K) * R.ι (pp σ (-1) 1 (1 - d)) := by
          rw [R.K_mul_K]; group
    _ = _ := by group

theorem rel_e : R.K * R.ι (pp σ 1 0 (1 + d)) * R.K * R.Jg * (R.ι (pp σ 1 0 (1 + d)))⁻¹ * R.K =
    R.ι (tY σ d) ^ 5 * R.Jg := by
  have h := R.base_mul_rel (a := PGammaL28.k * PGammaL28.y ^ 4 * PGammaL28.k * PGammaL28.j *
    (PGammaL28.y ^ 4)⁻¹ * PGammaL28.k) (b := PGammaL28.y ^ 5 * PGammaL28.j)
    (by simpa using pgl_rel_e)
  simp only [map_mul, map_inv, map_pow, R.base_k, R.base_y, R.base_j] at h
  rw [← tY_pow_four σ d, map_pow]
  exact h

theorem KJ_fixes_Y4
    [Finite k] : R.act (some (1, 0, 1 + d)) (R.K * R.Jg) = some (1, 0, 1 + d) := by
  rw [act, rep]
  have h := R.rel_e
  have e : R.K * R.ι (ppv σ (1, 0, 1 + d)) * (R.K * R.Jg) =
      R.ι (tY σ d ^ 5 * ThompsonN.J σ) * R.K * R.ι (ppv σ (1, 0, 1 + d)) := by
    rw [map_mul, map_pow]
    change R.K * R.ι (pp σ 1 0 (1 + d)) * (R.K * R.Jg) = R.ι (tY σ d) ^ 5 * R.Jg * R.K *
      R.ι (pp σ 1 0 (1 + d))
    rw [← h]
    calc R.K * R.ι (pp σ 1 0 (1 + d)) * (R.K * R.Jg) = R.K * R.ι (pp σ 1 0 (1 + d)) * R.K *
          R.Jg * (R.ι (pp σ 1 0 (1 + d)))⁻¹ * (R.K * R.K) * R.ι (pp σ 1 0 (1 + d)) := by
            rw [R.K_mul_K]; group
      _ = _ := by group
  rw [e, R.pt_pres]

end RType

end CFSG.Walter.Ree.T2
