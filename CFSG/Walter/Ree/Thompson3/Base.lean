module

public import CFSG.Walter.Ree.Thompson3.Action

public section

namespace CFSG.Walter.Ree.T2

theorem pgl_rel_a : pglK * (pglT⁻¹ * pglY ^ 3) * pglK * (pglT⁻¹ * pglY ^ 3)⁻¹ * pglK =
    pglY ^ 2 * pglJ := by decide

theorem pgl_rel_b : pglK * (pglY * pglT) * pglJ * pglK * (pglY * pglT)⁻¹ * pglK =
    pglY ^ 6 * pglJ := by decide

theorem pgl_rel_c : pglK * pglY⁻¹ * pglT * pglK = pglY ^ 3 * pglK * pglY * pglT := by decide

theorem pglJ_mul_pglK : pglJ * pglK = pglK * pglJ := by decide

@[simp] theorem PGammaL28.coe_j : (PGammaL28.j : Equiv.Perm (Fin 9)) = pglJ := rfl

@[simp] theorem PGammaL28.coe_k : (PGammaL28.k : Equiv.Perm (Fin 9)) = pglK := rfl

@[simp] theorem PGammaL28.coe_t : (PGammaL28.t : Equiv.Perm (Fin 9)) = pglT := rfl

@[simp] theorem PGammaL28.coe_y : (PGammaL28.y : Equiv.Perm (Fin 9)) = pglY := rfl

variable {k : Type} [Field k] [CharP k 3]

theorem three_eq_zero' : (3 : k) = 0 := ThompsonN.three_eq_zero

theorem tY_sq (σ : k ≃+* k) (d : k) : tY σ d ^ 2 = pp σ (-1) 0 (1 - d) := by
  simp only [sq, tY, pp]
  rw [ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp only; linear_combination h3
  · simp only [map_one]; ring
  · simp only [map_one]; linear_combination d * h3

theorem tY_cube (σ : k ≃+* k) (d : k) : tY σ d ^ 3 = pp σ 0 0 1 := by
  rw [pow_succ, tY_sq]
  simp only [tY, pp]
  rw [ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp only; ring
  · simp only [map_one, map_neg]; ring
  · simp only [map_one, map_neg]; linear_combination (-1 : k) * h3

theorem tT_inv_mul_tY_cube (σ : k ≃+* k) (d : k) :
    (tT σ)⁻¹ * tY σ d ^ 3 = pp σ 0 (-1) 1 := by
  rw [tY_cube]
  simp only [tT, pp]
  rw [ThompsonN.inv_P, ThompsonN.mul_P]
  simp

theorem tY_mul_tT (σ : k ≃+* k) (d : k) : tY σ d * tT σ = pp σ 1 1 d := by
  simp only [tY, tT, pp]
  rw [ThompsonN.mul_P]
  simp

namespace RType

variable [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

@[expose] noncomputable def Jg : G := R.ι (ThompsonN.J σ)

omit [Finite k] in
theorem base_mul_rel {a b : PGammaL28} (h : (a : Equiv.Perm (Fin 9)) = b) : R.base a = R.base b :=
  congrArg R.base (Subtype.ext h)

omit [Finite k] in
theorem rel_a : R.K * R.ι (pp σ 0 (-1) 1) * R.K * (R.ι (pp σ 0 (-1) 1))⁻¹ * R.K =
    R.ι (tY σ d) ^ 2 * R.Jg := by
  have h := R.base_mul_rel (a := PGammaL28.k * (PGammaL28.t⁻¹ * PGammaL28.y ^ 3) * PGammaL28.k *
    (PGammaL28.t⁻¹ * PGammaL28.y ^ 3)⁻¹ * PGammaL28.k) (b := PGammaL28.y ^ 2 * PGammaL28.j)
    (by simpa using pgl_rel_a)
  simp only [map_mul, map_inv, map_pow, R.base_k, R.base_t, R.base_y, R.base_j] at h
  rw [← tT_inv_mul_tY_cube σ d, map_mul, map_inv, map_pow]
  exact h

omit [Finite k] in
theorem rel_b : R.K * R.ι (pp σ 1 1 d) * R.Jg * R.K * (R.ι (pp σ 1 1 d))⁻¹ * R.K =
    R.ι (tY σ d) ^ 6 * R.Jg := by
  have h := R.base_mul_rel (a := PGammaL28.k * (PGammaL28.y * PGammaL28.t) * PGammaL28.j *
    PGammaL28.k * (PGammaL28.y * PGammaL28.t)⁻¹ * PGammaL28.k) (b := PGammaL28.y ^ 6 * PGammaL28.j)
    (by simpa using pgl_rel_b)
  simp only [map_mul, map_inv, map_pow, R.base_k, R.base_t, R.base_y, R.base_j] at h
  rw [← tY_mul_tT σ d, map_mul]
  exact h

omit [Finite k] in
theorem rel_c : R.K * (R.ι (tY σ d))⁻¹ * R.ι (tT σ) * R.K =
    R.ι (tY σ d) ^ 3 * R.K * R.ι (tY σ d) * R.ι (tT σ) := by
  have h := R.base_mul_rel (a := PGammaL28.k * PGammaL28.y⁻¹ * PGammaL28.t * PGammaL28.k)
    (b := PGammaL28.y ^ 3 * PGammaL28.k * PGammaL28.y * PGammaL28.t) (by simpa using pgl_rel_c)
  simp only [map_mul, map_inv, map_pow, R.base_k, R.base_t, R.base_y] at h
  exact h

omit [Finite k] in
theorem Jg_mul_K : R.Jg * R.K = R.K * R.Jg := by
  have h := R.base_mul_rel (a := PGammaL28.j * PGammaL28.k) (b := PGammaL28.k * PGammaL28.j)
    (by simpa using pglJ_mul_pglK)
  simp only [map_mul, R.base_k, R.base_j] at h
  exact h

theorem K_fixes_a :
    R.act (some (0, -1, 1)) R.K = some (0, -1, 1) := by
  apply R.act_K_of_eq (ν := tY σ d ^ 2 * ThompsonN.J σ)
  have h := R.rel_a
  rw [map_mul, map_pow]
  change R.K * R.ι (pp σ 0 (-1) 1) * R.K = R.ι (tY σ d) ^ 2 * R.Jg * R.K * R.ι (pp σ 0 (-1) 1)
  rw [← h]
  calc R.K * R.ι (pp σ 0 (-1) 1) * R.K = R.K * R.ι (pp σ 0 (-1) 1) * R.K *
        (R.ι (pp σ 0 (-1) 1))⁻¹ * (R.K * R.K) * R.ι (pp σ 0 (-1) 1) := by
          rw [R.K_mul_K]; group
    _ = _ := by group

theorem JK_fixes_b :
    R.act (some (1, 1, d)) (R.Jg * R.K) = some (1, 1, d) := by
  rw [act, rep]
  have h := R.rel_b
  have e : R.K * R.ι (ppv σ (1, 1, d)) * (R.Jg * R.K) =
      R.ι (tY σ d ^ 6 * ThompsonN.J σ) * R.K * R.ι (ppv σ (1, 1, d)) := by
    rw [map_mul, map_pow]
    change R.K * R.ι (pp σ 1 1 d) * (R.Jg * R.K) = R.ι (tY σ d) ^ 6 * R.Jg * R.K *
      R.ι (pp σ 1 1 d)
    rw [← h]
    calc R.K * R.ι (pp σ 1 1 d) * (R.Jg * R.K) = R.K * R.ι (pp σ 1 1 d) * R.Jg * R.K *
          (R.ι (pp σ 1 1 d))⁻¹ * (R.K * R.K) * R.ι (pp σ 1 1 d) := by
            rw [R.K_mul_K]; group
      _ = _ := by group
  rw [e, R.pt_pres]

end RType

end CFSG.Walter.Ree.T2
