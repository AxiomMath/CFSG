module

public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Unitary Matrix

open scoped MatrixGroups

structure ggNSPosPF3C_ShearData {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) (ω : K)
    (X Y c : GL (Fin n) K) : Prop where
  omega : ω ^ 2 + ω + 1 = 0
  sigma_omega : σ ω = ω ^ 2
  X_cube : X ^ 3 = 1
  X_unitary : conjTr σ (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) = 1
  c_unitary : conjTr σ (c : Matrix (Fin n) (Fin n) K) * (c : Matrix (Fin n) (Fin n) K) = 1
  YX : (Y : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) =
    ω • ((X : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K))
  cX : (c : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) =
    (X : Matrix (Fin n) (Fin n) K) * (c : Matrix (Fin n) (Fin n) K)
  cY : (c : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K) =
    (Y : Matrix (Fin n) (Fin n) K) * (c : Matrix (Fin n) (Fin n) K)
  c_quad : (c : Matrix (Fin n) (Fin n) K) * (c : Matrix (Fin n) (Fin n) K) =
    ω ^ 2 • (c : Matrix (Fin n) (Fin n) K) + ω • (1 : Matrix (Fin n) (Fin n) K)
  c_nonscalar : ∀ a : K, (c : Matrix (Fin n) (Fin n) K) ≠ a • (1 : Matrix (Fin n) (Fin n) K)

section Idempotents

variable {K : Type} [Field K] {n : ℕ}

@[expose] def ggNSPosPF3C_P2 (ω : K) (c : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  ω • (c + 1)

@[expose] def ggNSPosPF3C_P1 (ω : K) (c : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  1 + ggNSPosPF3C_P2 ω c

variable [CharP K 2] {ω : K} {c : Matrix (Fin n) (Fin n) K}

open scoped CharTwo

private theorem ggNSPosPF3C_eq_of_add_self {R : Type*} [Ring R] [CharP R 2] {a b : R}
    (h : a + b = 0) : a = b := by
  simpa using (CharTwo.add_eq_iff_eq_add.mp h)

private theorem ggNSPosPF3C_omega_sq (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 2 = ω + 1 := by
  refine ggNSPosPF3C_eq_of_add_self ?_
  simpa only [add_assoc] using hω

private theorem ggNSPosPF3C_omega_cube (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have hsq := ggNSPosPF3C_omega_sq hω
  calc ω ^ 3 = ω * ω ^ 2 := by ring
    _ = ω * (ω + 1) := by rw [hsq]
    _ = ω ^ 2 + ω := by ring
    _ = 1 := ggNSPosPF3C_eq_of_add_self hω

private theorem ggNSPosPF3C_omega_four (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 4 = ω := by
  calc ω ^ 4 = ω * ω ^ 3 := by ring
    _ = ω := by rw [ggNSPosPF3C_omega_cube hω, mul_one]

private theorem ggNSPosPF3C_omega_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  have h3 := ggNSPosPF3C_omega_cube hω
  rw [h, zero_pow (by norm_num : 3 ≠ 0)] at h3
  exact zero_ne_one h3

private theorem ggNSPosPF3C_one_add_omega (hω : ω ^ 2 + ω + 1 = 0) : 1 + ω = ω ^ 2 := by
  refine ggNSPosPF3C_eq_of_add_self ?_
  linear_combination hω

private theorem ggNSPosPF3C_omega_add_sq (hω : ω ^ 2 + ω + 1 = 0) : ω + ω ^ 2 = 1 := by
  refine ggNSPosPF3C_eq_of_add_self ?_
  linear_combination hω

private theorem ggNSPosPF3C_one_add_sq (hω : ω ^ 2 + ω + 1 = 0) : 1 + ω ^ 2 = ω := by
  refine ggNSPosPF3C_eq_of_add_self ?_
  linear_combination hω

private theorem ggNSPosPF3C_add_self (M : Matrix (Fin n) (Fin n) K) : M + M = 0 := by
  rw [← two_smul K M, CharTwo.two_eq_zero, zero_smul]

private theorem ggNSPosPF3C_matrix_eq_of_add_self {a b : Matrix (Fin n) (Fin n) K}
    (h : a + b = 0) : a = b := by
  calc a = a + 0 := (add_zero a).symm
    _ = a + (b + b) := by rw [ggNSPosPF3C_add_self]
    _ = (a + b) + b := by abel
    _ = 0 + b := by rw [h]
    _ = b := zero_add b

private theorem ggNSPosPF3C_conjTr_smul (σ : K ≃+* K) (a : K)
    (A : Matrix (Fin n) (Fin n) K) :
    conjTr σ (a • A) = σ a • conjTr σ A := by
  ext i j
  simp [conjTr, Matrix.map_smul]

private theorem ggNSPosPF3C_P2_eq (ω : K) (c : Matrix (Fin n) (Fin n) K) :
    ggNSPosPF3C_P2 ω c = ω • c + ω • 1 := by
  simp [ggNSPosPF3C_P2, smul_add]

private theorem ggNSPosPF3C_P1_eq (ω : K) (c : Matrix (Fin n) (Fin n) K) :
    ggNSPosPF3C_P1 ω c = ω • c + (1 + ω) • 1 := by
  simp only [ggNSPosPF3C_P1, ggNSPosPF3C_P2, smul_add]
  rw [add_smul, one_smul]
  abel

private theorem ggNSPosPF3C_lin_mul
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K))
    (a b a' b' : K) :
    (a • c + b • 1) * (a' • c + b' • 1) =
      (a * a' * ω ^ 2 + a * b' + a' * b) • c + (a * a' * ω + b * b') • 1 := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [hc]
  module

private theorem ggNSPosPF3C_lin_add (a b a' b' : K) :
    (a • c + b • 1) + (a' • c + b' • 1) = (a + a') • c + (b + b') • 1 := by
  module

private theorem ggNSPosPF3C_lin_smul (x a b : K) :
    x • (a • c + b • 1) = (x * a) • c + (x * b) • 1 := by
  rw [smul_add, smul_smul, smul_smul]

private theorem ggNSPosPF3C_move_add {a b a' b' : K}
    {u v : Matrix (Fin n) (Fin n) K}
    (h : a • u + b • v = a' • u + b' • v) :
    (a + a') • u = (b + b') • v := by
  have h'' : (a • u + a' • u) + (b • v + b' • v) = 0 := by
    calc (a • u + a' • u) + (b • v + b' • v)
        = (a • u + b • v) + (a' • u + b' • v) := by abel
      _ = (a' • u + b' • v) + (a' • u + b' • v) := by
            exact congrArg (fun w => w + (a' • u + b' • v)) h
      _ = 0 := ggNSPosPF3C_add_self _
  rw [add_smul, add_smul]
  exact ggNSPosPF3C_matrix_eq_of_add_self h''

theorem ggNSPosPF3C_P2_mul_self (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) :
    ggNSPosPF3C_P2 ω c * ggNSPosPF3C_P2 ω c = ggNSPosPF3C_P2 ω c := by
  rw [ggNSPosPF3C_P2_eq]
  rw [ggNSPosPF3C_lin_mul hc]
  have h1 : ω * ω * ω ^ 2 + ω * ω + ω * ω = ω := by
    rw [show ω * ω * ω ^ 2 = ω ^ 4 by ring, ggNSPosPF3C_omega_four hω]
    simp [CharTwo.add_self_eq_zero]
  have h2 : ω * ω * ω + ω * ω = ω := by
    rw [show ω * ω * ω = ω ^ 3 by ring, ggNSPosPF3C_omega_cube hω,
      show ω * ω = ω ^ 2 by ring, ggNSPosPF3C_one_add_sq hω]
  rw [h1, h2]

theorem ggNSPosPF3C_P1_mul_self (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) :
    ggNSPosPF3C_P1 ω c * ggNSPosPF3C_P1 ω c = ggNSPosPF3C_P1 ω c := by
  rw [ggNSPosPF3C_P1_eq]
  rw [ggNSPosPF3C_lin_mul hc]
  have h1 : ω * ω * ω ^ 2 + ω * (1 + ω) + ω * (1 + ω) = ω := by
    rw [show ω * ω * ω ^ 2 = ω ^ 4 by ring, ggNSPosPF3C_omega_four hω]
    simp [CharTwo.add_self_eq_zero]
  have h2 : ω * ω * ω + (1 + ω) * (1 + ω) = 1 + ω := by
    rw [show ω * ω * ω = ω ^ 3 by ring, ggNSPosPF3C_omega_cube hω,
      show (1 + ω) * (1 + ω) = (1 + ω) ^ 2 by ring, CharTwo.add_sq, one_pow,
      ggNSPosPF3C_one_add_sq hω, ggNSPosPF3C_one_add_omega hω]
  rw [h1, h2]

theorem ggNSPosPF3C_P1_mul_P2 (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) :
    ggNSPosPF3C_P1 ω c * ggNSPosPF3C_P2 ω c = 0 := by
  rw [ggNSPosPF3C_P1_eq]
  rw [ggNSPosPF3C_P2_eq]
  rw [ggNSPosPF3C_lin_mul hc]
  have h1 : ω * ω * ω ^ 2 + ω * ω + ω * (1 + ω) = 0 := by
    rw [show ω * ω * ω ^ 2 = ω ^ 4 by ring, ggNSPosPF3C_omega_four hω,
      show ω * ω = ω ^ 2 by ring, show ω * (1 + ω) = ω + ω ^ 2 by ring,
      CharTwo.add_self_eq_zero]
  have h2 : ω * ω * ω + (1 + ω) * ω = 0 := by
    rw [show ω * ω * ω = ω ^ 3 by ring, ggNSPosPF3C_omega_cube hω,
      show (1 + ω) * ω = ω + ω ^ 2 by ring, ggNSPosPF3C_omega_add_sq hω,
      CharTwo.add_self_eq_zero]
  rw [h1, h2, zero_smul, zero_smul, add_zero]

theorem ggNSPosPF3C_P2_mul_P1 (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) :
    ggNSPosPF3C_P2 ω c * ggNSPosPF3C_P1 ω c = 0 := by
  rw [ggNSPosPF3C_P2_eq]
  rw [ggNSPosPF3C_P1_eq]
  rw [ggNSPosPF3C_lin_mul hc]
  have h1 : ω * ω * ω ^ 2 + ω * (1 + ω) + ω * ω = 0 := by
    rw [show ω * ω * ω ^ 2 = ω ^ 4 by ring, ggNSPosPF3C_omega_four hω,
      show ω * (1 + ω) = ω + ω ^ 2 by ring, show ω * ω = ω ^ 2 by ring]
    simp [CharTwo.add_self_eq_zero]
  have h2 : ω * ω * ω + ω * (1 + ω) = 0 := by
    rw [show ω * ω * ω = ω ^ 3 by ring, ggNSPosPF3C_omega_cube hω,
      show ω * (1 + ω) = ω + ω ^ 2 by ring, ggNSPosPF3C_omega_add_sq hω,
      CharTwo.add_self_eq_zero]
  rw [h1, h2, zero_smul, zero_smul, add_zero]

theorem ggNSPosPF3C_P1_add_P2 :
    ggNSPosPF3C_P1 ω c + ggNSPosPF3C_P2 ω c = 1 := by
  rw [ggNSPosPF3C_P1, add_assoc, ggNSPosPF3C_add_self, add_zero]

theorem ggNSPosPF3C_P1_add_smul_P2 (hω : ω ^ 2 + ω + 1 = 0) :
    ggNSPosPF3C_P1 ω c + ω • ggNSPosPF3C_P2 ω c = c := by
  rw [ggNSPosPF3C_P1_eq]
  rw [ggNSPosPF3C_P2_eq]
  rw [ggNSPosPF3C_lin_smul]
  rw [ggNSPosPF3C_lin_add]
  have h1 : ω + ω * ω = 1 := by
    rw [show ω * ω = ω ^ 2 by ring, ggNSPosPF3C_omega_add_sq hω]
  have h2 : (1 + ω) + ω * ω = 0 := by
    rw [show ω * ω = ω ^ 2 by ring]
    linear_combination hω
  rw [h1, h2, zero_smul, one_smul, add_zero]

private theorem ggNSPosPF3C_mul_step (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) (j : ℕ) :
    (ggNSPosPF3C_P1 ω c + ω ^ j • ggNSPosPF3C_P2 ω c) *
        (ggNSPosPF3C_P1 ω c + ω • ggNSPosPF3C_P2 ω c) =
      ggNSPosPF3C_P1 ω c + ω ^ (j + 1) • ggNSPosPF3C_P2 ω c := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ggNSPosPF3C_P1_mul_self hω hc, ggNSPosPF3C_P2_mul_self hω hc,
    ggNSPosPF3C_P1_mul_P2 hω hc, ggNSPosPF3C_P2_mul_P1 hω hc]
  rw [smul_zero, smul_zero, zero_add, add_zero, ← pow_succ]

theorem ggNSPosPF3C_pow_eq (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) (j : ℕ) :
    c ^ j = ggNSPosPF3C_P1 ω c + ω ^ j • ggNSPosPF3C_P2 ω c := by
  induction j with
  | zero =>
      rw [pow_zero, pow_zero, one_smul, ggNSPosPF3C_P1_add_P2]
  | succ j ih =>
      rw [pow_succ, ih]
      have hstep := congrArg
        (fun X => (ggNSPosPF3C_P1 ω c + ω ^ j • ggNSPosPF3C_P2 ω c) * X)
        (ggNSPosPF3C_P1_add_smul_P2 (ω := ω) (c := c) hω)
      rw [← hstep, ggNSPosPF3C_mul_step hω hc j]

theorem ggNSPosPF3C_pow_three (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K)) :
    c ^ 3 = 1 := by
  rw [ggNSPosPF3C_pow_eq hω hc 3, ggNSPosPF3C_omega_cube hω, one_smul,
    ggNSPosPF3C_P1_add_P2]

theorem ggNSPosPF3C_commute_P {ℓ : Matrix (Fin n) (Fin n) K} (hℓ : ℓ * c = c * ℓ) :
    ℓ * ggNSPosPF3C_P1 ω c = ggNSPosPF3C_P1 ω c * ℓ ∧
      ℓ * ggNSPosPF3C_P2 ω c = ggNSPosPF3C_P2 ω c * ℓ := by
  have h2 : ℓ * ggNSPosPF3C_P2 ω c = ggNSPosPF3C_P2 ω c * ℓ := by
    rw [ggNSPosPF3C_P2_eq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, smul_add, hℓ]
  refine ⟨?_, h2⟩
  rw [ggNSPosPF3C_P1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, h2]

theorem ggNSPosPF3C_conjTr_P (σ : K ≃+* K) (hσ : σ ω = ω ^ 2) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K))
    (hcu : conjTr σ c * c = 1) :
    conjTr σ (ggNSPosPF3C_P1 ω c) = ggNSPosPF3C_P1 ω c ∧
      conjTr σ (ggNSPosPF3C_P2 ω c) = ggNSPosPF3C_P2 ω c := by
  have hc3 : c ^ 3 = 1 := ggNSPosPF3C_pow_three hω hc
  have hc3' : (c * c) * c = 1 := by
    rw [← pow_two, ← pow_succ]
    exact hc3
  have hconj : conjTr σ c = ω ^ 2 • c + ω • 1 := by
    calc conjTr σ c = conjTr σ c * 1 := (mul_one _).symm
      _ = conjTr σ c * ((c * c) * c) := by rw [hc3']
      _ = (conjTr σ c * c) * (c * c) := by noncomm_ring
      _ = 1 * (c * c) := by rw [hcu]
      _ = c * c := one_mul _
      _ = ω ^ 2 • c + ω • 1 := hc
  have hP2 : conjTr σ (ggNSPosPF3C_P2 ω c) = ggNSPosPF3C_P2 ω c := by
    rw [ggNSPosPF3C_P2_eq]
    rw [conjTr_add, ggNSPosPF3C_conjTr_smul, ggNSPosPF3C_conjTr_smul, conjTr_one, hσ, hconj]
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
    rw [show ω ^ 2 * ω ^ 2 = ω by
          rw [show ω ^ 2 * ω ^ 2 = ω ^ 4 by ring, ggNSPosPF3C_omega_four hω],
      show ω ^ 2 * ω + ω ^ 2 = ω by
          rw [show ω ^ 2 * ω = ω ^ 3 by ring, ggNSPosPF3C_omega_cube hω,
            ggNSPosPF3C_one_add_sq hω]]
  refine ⟨?_, hP2⟩
  rw [ggNSPosPF3C_P1, conjTr_add, conjTr_one, hP2]

theorem ggNSPosPF3C_scalar_eq_one_of_conj (hω : ω ^ 2 + ω + 1 = 0)
    (hc : c * c = ω ^ 2 • c + ω • (1 : Matrix (Fin n) (Fin n) K))
    (hns : ∀ a : K, c ≠ a • (1 : Matrix (Fin n) (Fin n) K))
    {ℓ : GL (Fin n) K} {ζ : Kˣ} (h : (ℓ : Matrix (Fin n) (Fin n) K) * c = (ζ : K) • (c * ℓ)) :
    ζ = 1 := by
  by_contra hζ
  have h1ζ : (1 : K) + (ζ : K) ≠ 0 := by
    intro hh
    apply hζ
    apply Units.ext
    have hz : (ζ : K) = 1 := by
      simpa using (CharTwo.add_eq_iff_eq_add.mp hh).symm
    exact hz
  have h1 : (ℓ : Matrix (Fin n) (Fin n) K) * (c * c) =
      (ζ : K) ^ 2 • ((c * c) * (ℓ : Matrix (Fin n) (Fin n) K)) := by
    calc (ℓ : Matrix (Fin n) (Fin n) K) * (c * c)
        = ((ℓ : Matrix (Fin n) (Fin n) K) * c) * c := by rw [Matrix.mul_assoc]
      _ = ((ζ : K) • (c * (ℓ : Matrix (Fin n) (Fin n) K))) * c := by rw [h]
      _ = (ζ : K) • ((c * (ℓ : Matrix (Fin n) (Fin n) K)) * c) := by rw [Matrix.smul_mul]
      _ = (ζ : K) • (c * ((ℓ : Matrix (Fin n) (Fin n) K) * c)) := by rw [Matrix.mul_assoc]
      _ = (ζ : K) • (c * ((ζ : K) • (c * (ℓ : Matrix (Fin n) (Fin n) K)))) := by rw [h]
      _ = (ζ : K) • ((ζ : K) • (c * (c * (ℓ : Matrix (Fin n) (Fin n) K)))) := by
            rw [Matrix.mul_smul]
      _ = (ζ : K) • ((ζ : K) • ((c * c) * (ℓ : Matrix (Fin n) (Fin n) K))) := by
            rw [← Matrix.mul_assoc]
      _ = (ζ : K) ^ 2 • ((c * c) * (ℓ : Matrix (Fin n) (Fin n) K)) := by
            rw [smul_smul, ← pow_two]
  have hL : (ℓ : Matrix (Fin n) (Fin n) K) * (c * c) =
      (ω ^ 2 * (ζ : K)) • (c * (ℓ : Matrix (Fin n) (Fin n) K)) +
        ω • (ℓ : Matrix (Fin n) (Fin n) K) := by
    rw [hc]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, h, smul_add, smul_smul]
  have hR : (c * c) * (ℓ : Matrix (Fin n) (Fin n) K) =
      ω ^ 2 • (c * (ℓ : Matrix (Fin n) (Fin n) K)) +
        ω • (ℓ : Matrix (Fin n) (Fin n) K) := by
    rw [hc]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
  have hmain : (ω ^ 2 * (ζ : K)) • (c * (ℓ : Matrix (Fin n) (Fin n) K)) +
        ω • (ℓ : Matrix (Fin n) (Fin n) K) =
      ((ζ : K) ^ 2 * ω ^ 2) • (c * (ℓ : Matrix (Fin n) (Fin n) K)) +
        ((ζ : K) ^ 2 * ω) • (ℓ : Matrix (Fin n) (Fin n) K) := by
    rw [← hL, h1, hR]
    simp only [smul_add, smul_smul]
  have hm : (ω ^ 2 * (ζ : K)) • c + ω • (1 : Matrix (Fin n) (Fin n) K) =
      ((ζ : K) ^ 2 * ω ^ 2) • c + ((ζ : K) ^ 2 * ω) • (1 : Matrix (Fin n) (Fin n) K) := by
    have h' := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
      M * ((ℓ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hmain
    simpa [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, Units.val_mul, Units.val_one,
      mul_inv_cancel, Matrix.mul_one] using h'
  have hkey : (ω ^ 2 * (ζ : K) + (ζ : K) ^ 2 * ω ^ 2) • c =
      (ω + (ζ : K) ^ 2 * ω) • (1 : Matrix (Fin n) (Fin n) K) :=
    ggNSPosPF3C_move_add hm
  have hP : ω ^ 2 * (ζ : K) + (ζ : K) ^ 2 * ω ^ 2 ≠ 0 := by
    have hfac : ω ^ 2 * (ζ : K) + (ζ : K) ^ 2 * ω ^ 2 =
        ω ^ 2 * (ζ : K) * (1 + (ζ : K)) := by ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ggNSPosPF3C_omega_ne_zero hω))
      ζ.ne_zero) h1ζ
  have hc_scalar : c = ((ω ^ 2 * (ζ : K) + (ζ : K) ^ 2 * ω ^ 2)⁻¹ *
      (ω + (ζ : K) ^ 2 * ω)) • (1 : Matrix (Fin n) (Fin n) K) := by
    have h' := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
      (ω ^ 2 * (ζ : K) + (ζ : K) ^ 2 * ω ^ 2)⁻¹ • M) hkey
    simpa [smul_smul, hP, inv_mul_cancel₀, one_smul] using h'
  exact hns _ hc_scalar

end Idempotents

end CFSG.StandardType

end
