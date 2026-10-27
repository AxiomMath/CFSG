module

public import CFSG.Monster.Lagrangian
public import CFSG.Monster.Dyadic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.Monster

open Module Matrix

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] [DecidableEq E]

@[expose] def fourierMatrix (b : LinearMap.BilinForm (ZMod 2) E) (m : ℕ) : Matrix E E ℚ :=
  fun u v => ((2 : ℚ) ^ m)⁻¹ * sgn (b u v)

@[expose] def signMatrix (q : E → ZMod 2) : Matrix E E ℚ := Matrix.diagonal fun u => sgn (q u)

theorem sgn_mul_self (t : ZMod 2) : sgn t * sgn t = 1 := by
  fin_cases t <;> simp [sgn] <;> decide

omit [AddCommGroup E] [Module (ZMod 2) E] in
theorem signMatrix_mul_self (q : E → ZMod 2) : signMatrix q * signMatrix q = 1 := by
  rw [signMatrix, Matrix.diagonal_mul_diagonal]
  simp only [sgn_mul_self]
  exact Matrix.diagonal_one

omit [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] in
theorem signMatrix_transpose (q : E → ZMod 2) : (signMatrix q)ᵀ = signMatrix q :=
  Matrix.diagonal_transpose _

omit [Fintype E] [DecidableEq E] in
theorem fourierMatrix_transpose {b : LinearMap.BilinForm (ZMod 2) E} (halt : ∀ v, b v v = 0)
    (m : ℕ) : (fourierMatrix b m)ᵀ = fourierMatrix b m := by
  ext u v
  simp [fourierMatrix, symm_of_alternating halt u v]

theorem sum_sgn_bilin {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.Nondegenerate) (w : E) :
    ∑ v, sgn (b w v) = if w = 0 then (Fintype.card E : ℚ) else 0 := by
  classical
  split_ifs with h
  · subst h; simp [sgn]
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, b w v₀ ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (hb.1 w hc)
    have := sum_sgn_of_not_perp b ⊤ (Submodule.mem_top (x := v₀)) hv₀
    rw [← this]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun x => Submodule.mem_top) _ _
      fun x => rfl).symm

section Quadratic

variable (Q : QuadraticForm (ZMod 2) E)

omit [Fintype E] [DecidableEq E] in
theorem polarBilin_self (v : E) : QuadraticMap.polarBilin Q v v = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  have : (2 : ZMod 2) = 0 := rfl
  simp [this]

omit [Fintype E] [DecidableEq E] in
theorem quad_add (u v : E) : Q (u + v) = Q u + Q v + QuadraticMap.polarBilin Q u v := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

omit [Fintype E] [DecidableEq E] in
theorem polarBilin_symm (u v : E) :
    QuadraticMap.polarBilin Q u v = QuadraticMap.polarBilin Q v u :=
  symm_of_alternating (polarBilin_self Q) u v

theorem fourierMatrix_mul_self (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hE : Fintype.card E = 2 ^ (2 * m)) :
    fourierMatrix (QuadraticMap.polarBilin Q) m * fourierMatrix (QuadraticMap.polarBilin Q) m =
      1 := by
  ext u w
  simp only [Matrix.mul_apply, fourierMatrix]
  have h : ∀ v, ((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q u v) *
      (((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q v w)) =
      ((2 : ℚ) ^ m)⁻¹ * ((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q (u + w) v) := by
    intro v
    rw [map_add, LinearMap.add_apply, sgn_add, polarBilin_symm Q v w]
    ring
  rw [Finset.sum_congr rfl (fun v _ => h v), ← Finset.mul_sum, sum_sgn_bilin hb]
  by_cases huw : u = w
  · subst huw
    have : u + u = 0 := by rw [← sub_eq_add_zmod_two, sub_self]
    simp only [this, ite_true, Matrix.one_apply_eq, hE]
    have h2 : ((2 ^ (2 * m) : ℕ) : ℚ) = (2 : ℚ) ^ m * (2 : ℚ) ^ m := by
      push_cast
      rw [two_mul, pow_add]
    rw [h2]
    field_simp
  · have : u + w ≠ 0 := fun h => huw (by rw [← sub_eq_zero, sub_eq_add_zmod_two]; exact h)
    simp only [this, ite_false, Matrix.one_apply_ne huw, mul_zero]

theorem fourier_sign_braid {m : ℕ} (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q *
        fourierMatrix (QuadraticMap.polarBilin Q) m =
      signMatrix Q * fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q := by
  ext u w
  rw [Matrix.mul_apply, signMatrix]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, fourierMatrix]
  have h : ∀ v, ((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q u v) * sgn (Q v) *
      (((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q v w)) =
      ((2 : ℚ) ^ m)⁻¹ * ((2 : ℚ) ^ m)⁻¹ * sgn (Q (u + w)) * sgn (Q (v + (u + w))) := by
    intro v
    have e1 : Q (v + (u + w)) = Q v + Q (u + w) +
        (QuadraticMap.polarBilin Q v u + QuadraticMap.polarBilin Q v w) := by
      rw [quad_add Q v (u + w), (QuadraticMap.polarBilin Q v).map_add u w]
    rw [e1, sgn_add, sgn_add, sgn_add, polarBilin_symm Q v u]
    have hsq := sgn_mul_self (Q (u + w))
    linear_combination (-(((2 : ℚ) ^ m)⁻¹ * ((2 : ℚ) ^ m)⁻¹ * sgn (Q v) *
      sgn (QuadraticMap.polarBilin Q u v) * sgn (QuadraticMap.polarBilin Q v w))) * hsq
  rw [Finset.sum_congr rfl (fun v _ => h v), ← Finset.mul_sum]
  rw [show ∑ v, sgn (Q (v + (u + w))) = ∑ v, sgn (Q v) from
    Fintype.sum_equiv (Equiv.addRight (u + w)) _ _ (fun v => rfl), hgauss]
  rw [quad_add Q u w, sgn_add, sgn_add]
  field_simp

theorem fourier_sign_cube (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) ^ 3 = 1 := by
  set H := fourierMatrix (QuadraticMap.polarBilin Q) m
  set D := signMatrix Q
  have hH : H * H = 1 := fourierMatrix_mul_self Q hb hE
  have hD : D * D = 1 := signMatrix_mul_self Q
  have hbr : H * D * H = D * H * D := fourier_sign_braid Q hgauss
  calc (H * D) ^ 3 = (H * D * H) * (D * H * D) := by
        rw [pow_succ, pow_two]; simp only [Matrix.mul_assoc]
    _ = (D * H * D) * (D * H * D) := by rw [hbr]
    _ = 1 := by
        calc D * H * D * (D * H * D) = D * H * (D * D) * H * D := by simp only [Matrix.mul_assoc]
          _ = D * (H * H) * D := by rw [hD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hH, Matrix.mul_one, hD]

theorem trace_fourier_sign {m : ℕ} (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    Matrix.trace (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) = 1 := by
  simp only [Matrix.trace, Matrix.diag, signMatrix, Matrix.mul_diagonal, fourierMatrix,
    polarBilin_self, sgn_zero, mul_one]
  rw [← Finset.mul_sum, hgauss]
  field_simp

omit [AddCommGroup E] [Module (ZMod 2) E] in
theorem toLin'_pow_eq (M : Matrix E E ℚ) (n : ℕ) :
    Matrix.toLin' (M ^ n) = (Matrix.toLin' M) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ n ih => rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ]; rfl

theorem fourier_sign_sq (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) ^ 2 =
      signMatrix Q * fourierMatrix (QuadraticMap.polarBilin Q) m := by
  set H := fourierMatrix (QuadraticMap.polarBilin Q) m
  set D := signMatrix Q
  have hH : H * H = 1 := fourierMatrix_mul_self Q hb hE
  have hbr : H * D * H = D * H * D := fourier_sign_braid Q hgauss
  calc (H * D) ^ 2 = H * (D * H * D) := by rw [pow_two]; simp only [Matrix.mul_assoc]
    _ = H * (H * D * H) := by rw [hbr]
    _ = D * H := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, Matrix.one_mul]

theorem finrank_ker_fourier_sign_sub_one (hb : (QuadraticMap.polarBilin Q).Nondegenerate)
    {m : ℕ} (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    finrank ℚ (LinearMap.ker (Matrix.toLin'
      (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q - 1))) =
      (2 ^ (2 * m) + 2) / 3 := by
  set τ := fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q with hτdef
  have h3 : τ ^ 3 = 1 := fourier_sign_cube Q hb hE hgauss
  have htr : Matrix.trace τ = 1 := trace_fourier_sign Q hgauss
  have htr2 : Matrix.trace (τ ^ 2) = 1 := by
    rw [fourier_sign_sq Q hb hE hgauss, Matrix.trace_mul_comm, ← hτdef, htr]
  set T : (E → ℚ) →ₗ[ℚ] (E → ℚ) := Matrix.toLin' τ with hT
  have hT3 : T ^ 3 = 1 := by
    rw [hT, ← toLin'_pow_eq, h3, Matrix.toLin'_one]
    rfl
  set P : (E → ℚ) →ₗ[ℚ] (E → ℚ) := (3 : ℚ)⁻¹ • (1 + T + T ^ 2) with hP
  have hPidem : IsIdempotentElem P := by
    have hT4 : T ^ 4 = T := by rw [pow_succ, hT3, one_mul]
    show P * P = P
    rw [hP, smul_mul_smul_comm]
    have : (1 + T + T ^ 2) * (1 + T + T ^ 2) = (3 : ℚ) • (1 + T + T ^ 2) := by
      have e : (1 + T + T ^ 2) * (1 + T + T ^ 2) = 1 + 2 • T + 3 • T ^ 2 + 2 • T ^ 3 + T ^ 4 := by
        noncomm_ring
      rw [e, hT3, hT4]
      rw [← Nat.cast_smul_eq_nsmul ℚ 2, ← Nat.cast_smul_eq_nsmul ℚ 3]
      module
    rw [this, smul_smul]
    norm_num
  have hrange : LinearMap.range P = LinearMap.ker (T - 1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      show (T * P) y = P y
      rw [hP, mul_smul_comm]
      congr 1
      have : T * (1 + T + T ^ 2) = 1 + T + T ^ 2 := by
        have e : T * (1 + T + T ^ 2) = T + T ^ 2 + T ^ 3 := by noncomm_ring
        rw [e, hT3]
        abel
      rw [this]
    · intro hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
      refine ⟨x, ?_⟩
      have hx2 : (T ^ 2) x = x := by rw [pow_two, Module.End.mul_apply, hx, hx]
      rw [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
        hx, hx2]
      module
  have hker : LinearMap.ker (Matrix.toLin' (τ - 1)) = LinearMap.ker (T - 1) := by
    rw [map_sub, Matrix.toLin'_one]
    rfl
  have htrace : LinearMap.trace ℚ (E → ℚ) P = finrank ℚ (LinearMap.range P) :=
    LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range P hPidem)
  have htrP : LinearMap.trace ℚ (E → ℚ) P = ((2 : ℚ) ^ (2 * m) + 2) / 3 := by
    rw [hP, map_smul, map_add, map_add, LinearMap.trace_one, hT, ← toLin'_pow_eq τ 2]
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ E), LinearMap.trace_eq_matrix_trace ℚ
      (Pi.basisFun ℚ E)]
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin',
      htr, htr2]
    rw [Module.finrank_fintype_fun_eq_card, hE]
    push_cast
    ring
  rw [hker, ← hrange]
  have hq : (finrank ℚ (LinearMap.range P) : ℚ) = ((2 : ℚ) ^ (2 * m) + 2) / 3 := by
    rw [← htrace, htrP]
  have hnat : 3 * finrank ℚ (LinearMap.range P) = 2 ^ (2 * m) + 2 := by
    have : (3 * finrank ℚ (LinearMap.range P) : ℚ) = ((2 ^ (2 * m) + 2 : ℕ) : ℚ) := by
      push_cast
      rw [hq]
      ring
    exact_mod_cast this
  omega

theorem orderOf_fourier_sign (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : 1 ≤ m) (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    orderOf (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (fourier_sign_cube Q hb hE hgauss) fun h1 => ?_
  have htr := trace_fourier_sign Q hgauss
  rw [h1, Matrix.trace_one, hE] at htr
  have : (2 : ℕ) ^ (2 * m) ≥ 4 := by
    calc (2 : ℕ) ^ (2 * m) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have h' : ((2 ^ (2 * m) : ℕ) : ℚ) = 1 := htr
  have : (2 ^ (2 * m) : ℕ) = 1 := by exact_mod_cast h'
  omega

theorem sgn_mem_dyadic (t : ZMod 2) : sgn t ∈ dyadic := by
  unfold sgn
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem inv_two_pow_mem_dyadic (m : ℕ) : ((2 : ℚ) ^ m)⁻¹ ∈ dyadic := by
  refine mem_dyadic.2 ⟨m, ?_⟩
  have : ((2 : ℚ) ^ m)⁻¹ = ((2 ^ m : ℕ) : ℚ)⁻¹ := by push_cast; rfl
  rw [this, Rat.inv_natCast_den]
  split_ifs <;> simp

omit [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] [DecidableEq E] in
theorem fourierMatrix_mem_dyadic' {b : E → E → ZMod 2} (m : ℕ) (u v : E) :
    ((2 : ℚ) ^ m)⁻¹ * sgn (b u v) ∈ dyadic :=
  dyadic.mul_mem (inv_two_pow_mem_dyadic m) (sgn_mem_dyadic _)

omit [Fintype E] [DecidableEq E] in
theorem fourierMatrix_mem_dyadic (b : LinearMap.BilinForm (ZMod 2) E) (m : ℕ) (u v : E) :
    fourierMatrix b m u v ∈ dyadic :=
  fourierMatrix_mem_dyadic' (b := fun x y => b x y) m u v

omit [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] in
theorem signMatrix_mem_dyadic (q : E → ZMod 2) (u v : E) : signMatrix q u v ∈ dyadic := by
  unfold signMatrix Matrix.diagonal
  simp only [Matrix.of_apply]
  split_ifs
  · exact sgn_mem_dyadic _
  · exact dyadic.zero_mem

omit [AddCommGroup E] [Module (ZMod 2) E] [DecidableEq E] in
theorem mul_mem_dyadic {M N : Matrix E E ℚ} (hM : ∀ u v, M u v ∈ dyadic)
    (hN : ∀ u v, N u v ∈ dyadic) (u v : E) : (M * N) u v ∈ dyadic := by
  rw [Matrix.mul_apply]
  exact dyadic.sum_mem fun w _ => dyadic.mul_mem (hM u w) (hN w v)

omit [AddCommGroup E] [Module (ZMod 2) E] [DecidableEq E] in
theorem vecMul_mem_dyadic {M : Matrix E E ℚ} (hM : ∀ u v, M u v ∈ dyadic) {x : E → ℚ}
    (hx : ∀ u, x u ∈ dyadic) (v : E) : Matrix.vecMul x M v ∈ dyadic := by
  simp only [Matrix.vecMul, dotProduct]
  exact dyadic.sum_mem fun u _ => dyadic.mul_mem (hx u) (hM u v)

theorem binary_quadratic_fourier_triality (Q : QuadraticForm (ZMod 2) E)
    (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) E = 2 * m) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    let H := fourierMatrix (QuadraticMap.polarBilin Q) m
    let D := signMatrix Q
    Hᵀ = H ∧ Dᵀ = D ∧ H * Hᵀ = 1 ∧ D * Dᵀ = 1 ∧ H * H = 1 ∧ D * D = 1 ∧
      H * D * H = D * H * D ∧ (H * D) ^ 3 = 1 ∧
      (∀ x : E → ℚ, (∀ u, x u ∈ dyadic) → ∀ v, Matrix.vecMul x H v ∈ dyadic ∧
        Matrix.vecMul x D v ∈ dyadic ∧ Matrix.vecMul x (H * D) v ∈ dyadic) ∧
      Matrix.trace (H * D) = 1 ∧
      finrank ℚ (LinearMap.ker (Matrix.toLin' (H * D - 1))) = (2 ^ (2 * m) + 2) / 3 ∧
      (1 ≤ m → orderOf (H * D) = 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : Fintype.card E = 2 ^ (2 * m) := by
    rw [← FiniteField.pow_finrank_eq_card 2 E, hdim]
  intro H D
  have hHt : Hᵀ = H := fourierMatrix_transpose (polarBilin_self Q) m
  have hDt : Dᵀ = D := signMatrix_transpose Q
  have hH : H * H = 1 := fourierMatrix_mul_self Q hb hE
  have hD : D * D = 1 := signMatrix_mul_self Q
  have hHd : ∀ u v, H u v ∈ dyadic := fourierMatrix_mem_dyadic _ m
  have hDd : ∀ u v, D u v ∈ dyadic := signMatrix_mem_dyadic Q
  refine ⟨hHt, hDt, by rw [hHt, hH], by rw [hDt, hD], hH, hD, fourier_sign_braid Q hgauss,
    fourier_sign_cube Q hb hE hgauss, fun x hx v => ⟨vecMul_mem_dyadic hHd hx v,
      vecMul_mem_dyadic hDd hx v, vecMul_mem_dyadic (mul_mem_dyadic hHd hDd) hx v⟩,
    trace_fourier_sign Q hgauss, finrank_ker_fourier_sign_sub_one Q hb hE hgauss,
    fun hm => orderOf_fourier_sign Q hb hm hE hgauss⟩

end Quadratic

end CFSG.Monster
