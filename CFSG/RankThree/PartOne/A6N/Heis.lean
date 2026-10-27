module

public import CFSG.RankThree.PartOne.A6N.Trace
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartOne.A6N

open Matrix

section Class2

variable {G : Type*} [Group G]

theorem mul_central_swap {c : G} (hc : c ∈ Subgroup.center G) (g w : G) :
    g * (c * w) = c * (g * w) := by
  rw [← mul_assoc, Subgroup.mem_center_iff.mp hc g, mul_assoc]

theorem mul_pow_comm_of_central {x y c : G} (hc : c ∈ Subgroup.center G)
    (hxy : x * y = c * (y * x)) (n : ℕ) : x * y ^ n = c ^ n * (y ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * y ^ (n + 1) = (x * y ^ n) * y := by rw [pow_succ, mul_assoc]
      _ = c ^ n * (y ^ n * x) * y := by rw [ih]
      _ = c ^ n * (y ^ n * (x * y)) := by simp only [mul_assoc]
      _ = c ^ n * (y ^ n * (c * (y * x))) := by rw [hxy]
      _ = c ^ n * (c * (y ^ n * (y * x))) := by rw [mul_central_swap hc]
      _ = c ^ (n + 1) * (y ^ (n + 1) * x) := by
        rw [pow_succ' c n, pow_succ y n, mul_central_swap hc (c ^ n)]
        simp only [mul_assoc]

theorem pow_mul_pow_comm_of_central {x y c : G} (hc : c ∈ Subgroup.center G)
    (hxy : x * y = c * (y * x)) (m n : ℕ) :
    x ^ m * y ^ n = c ^ (m * n) * (y ^ n * x ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc x ^ (m + 1) * y ^ n = x * (x ^ m * y ^ n) := by rw [pow_succ', mul_assoc]
      _ = x * (c ^ (m * n) * (y ^ n * x ^ m)) := by rw [ih]
      _ = c ^ (m * n) * (x * (y ^ n * x ^ m)) := by rw [mul_central_swap (Subgroup.pow_mem _ hc _)]
      _ = c ^ (m * n) * ((x * y ^ n) * x ^ m) := by rw [← mul_assoc x]
      _ = c ^ (m * n) * (c ^ n * (y ^ n * x) * x ^ m) := by rw [mul_pow_comm_of_central hc hxy]
      _ = c ^ ((m + 1) * n) * (y ^ n * x ^ (m + 1)) := by
        rw [add_mul, one_mul, pow_add, pow_succ' x m]
        simp only [mul_assoc]

theorem pair_mul_comm {x y c : G} (hc : c ∈ Subgroup.center G) (hxy : x * y = c * (y * x))
    (a b a' b' : ℕ) :
    (x ^ a * y ^ b) * (x ^ a' * y ^ b') =
      c ^ (((a * b' : ℕ) : ℤ) - ((a' * b : ℕ) : ℤ)) * ((x ^ a' * y ^ b') * (x ^ a * y ^ b)) := by
  have hz : ∀ n : ℤ, c ^ n ∈ Subgroup.center G := fun n => Subgroup.zpow_mem _ hc n
  have hswap : ∀ m n : ℕ, y ^ n * x ^ m = c ^ (-((m * n : ℕ) : ℤ)) * (x ^ m * y ^ n) := by
    intro m n
    have h2 := pow_mul_pow_comm_of_central hc hxy m n
    rw [zpow_neg, zpow_natCast, h2, inv_mul_cancel_left]
  have hL : (x ^ a * y ^ b) * (x ^ a' * y ^ b') =
      c ^ (-((a' * b : ℕ) : ℤ)) * (x ^ (a + a') * y ^ (b + b')) := by
    calc (x ^ a * y ^ b) * (x ^ a' * y ^ b') = x ^ a * (y ^ b * x ^ a') * y ^ b' := by
          simp only [mul_assoc]
      _ = x ^ a * (c ^ (-((a' * b : ℕ) : ℤ)) * (x ^ a' * y ^ b)) * y ^ b' := by
          rw [hswap a' b]
      _ = c ^ (-((a' * b : ℕ) : ℤ)) * (x ^ (a + a') * y ^ (b + b')) := by
          rw [mul_central_swap (hz _), pow_add, pow_add]
          simp only [mul_assoc]
  have hR : (x ^ a' * y ^ b') * (x ^ a * y ^ b) =
      c ^ (-((a * b' : ℕ) : ℤ)) * (x ^ (a' + a) * y ^ (b' + b)) := by
    calc (x ^ a' * y ^ b') * (x ^ a * y ^ b) = x ^ a' * (y ^ b' * x ^ a) * y ^ b := by
          simp only [mul_assoc]
      _ = x ^ a' * (c ^ (-((a * b' : ℕ) : ℤ)) * (x ^ a * y ^ b')) * y ^ b := by
          rw [hswap a b']
      _ = c ^ (-((a * b' : ℕ) : ℤ)) * (x ^ (a' + a) * y ^ (b' + b)) := by
          rw [mul_central_swap (hz _), pow_add, pow_add]
          simp only [mul_assoc]
  rw [hL, hR, add_comm a a', add_comm b b',
    ← mul_assoc (c ^ (((a * b' : ℕ) : ℤ) - ((a' * b : ℕ) : ℤ))), ← zpow_add]
  congr 2
  ring

end Class2

section Mat

variable {K : Type*} [Field K]

theorem trace_idem {n : ℕ} (f : Matrix (Fin n) (Fin n) K) (hf : f * f = f) :
    ∃ r : ℕ, r ≤ n ∧ Matrix.trace f = (r : K) := by
  let φ : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' f
  have hφ : ∀ v, φ (φ v) = φ v := by
    intro v
    change f.mulVec (f.mulVec v) = f.mulVec v
    rw [Matrix.mulVec_mulVec, hf]
  have hproj : LinearMap.IsProj (LinearMap.range φ) φ :=
    ⟨fun v => LinearMap.mem_range_self φ v, fun v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact hφ w⟩
  have h1 := hproj.trace
  refine ⟨Module.finrank K (LinearMap.range φ), ?_, ?_⟩
  · calc Module.finrank K (LinearMap.range φ) ≤ Module.finrank K (Fin n → K) :=
          Submodule.finrank_le _
      _ = n := by simp
  · rw [← h1]
    simp only [φ]
    rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n))]
    simp

end Mat

section Cube

variable {K : Type*} [Field K]

theorem trace_zero_of_cube {M : Matrix (Fin 3) (Fin 3) K} (hM3 : M * M * M = 1)
    (hdet : M.det = 1) (hns : ∀ c : K, M ≠ Matrix.scalar (Fin 3) c) : M.trace = 0 := by
  by_contra ht
  have hch := ch3 M
  rw [hM3, hdet, one_smul] at hch
  change 1 - M.trace • (M * M) + e2 M • M - 1 = 0 at hch
  have h1 : e2 M • M = M.trace • (M * M) := by
    rw [← sub_eq_zero]
    calc e2 M • M - M.trace • (M * M) = 1 - M.trace • (M * M) + e2 M • M - 1 := by abel
      _ = 0 := hch
  have h2 : e2 M • (1 : Matrix (Fin 3) (Fin 3) K) = M.trace • M := by
    have h3 := congrArg (fun A => (M * M) * A) h1
    simp only [Matrix.mul_smul] at h3
    have h5 : M * M * (M * M) = M := by
      calc M * M * (M * M) = M * (M * M * M) := by simp only [mul_assoc]
        _ = M := by rw [hM3, mul_one]
    rw [h5, hM3] at h3
    exact h3
  apply hns ((M.trace)⁻¹ * e2 M)
  calc M = (M.trace)⁻¹ • (M.trace • M) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = (M.trace)⁻¹ • (e2 M • (1 : Matrix (Fin 3) (Fin 3) K)) := by rw [h2]
    _ = ((M.trace)⁻¹ * e2 M) • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [smul_smul]
    _ = Matrix.scalar (Fin 3) ((M.trace)⁻¹ * e2 M) := by
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Cube

theorem commuting_cubes {K : Type*} [Field K] (X Y : Matrix (Fin 3) (Fin 3) K)
    (hXY : X * Y = Y * X) (hX3 : X * X * X = 1) (hY3 : Y * Y * Y = 1) (h9 : (9 : K) ≠ 0)
    (t1 : X.trace = 0) (t2 : (X * X).trace = 0) (t3 : Y.trace = 0) (t4 : (Y * Y).trace = 0)
    (t5 : (X * Y).trace = 0) (t6 : (X * (Y * Y)).trace = 0) (t7 : (X * X * Y).trace = 0)
    (t8 : (X * X * (Y * Y)).trace = 0) :
    ∃ r : ℕ, r ≤ 3 ∧ (9 : K) * r = 3 := by
  set eX : Matrix (Fin 3) (Fin 3) K := 1 + X + X * X with heX
  set eY : Matrix (Fin 3) (Fin 3) K := 1 + Y + Y * Y with heY
  have hXX : eX * eX = (3 : ℕ) • eX := by
    have : eX * eX = 1 + (2 : ℕ) • X + (3 : ℕ) • (X * X) + (2 : ℕ) • (X * X * X) +
        X * X * X * X := by rw [heX]; noncomm_ring
    rw [this, hX3, one_mul, heX]
    module
  have hYY : eY * eY = (3 : ℕ) • eY := by
    have : eY * eY = 1 + (2 : ℕ) • Y + (3 : ℕ) • (Y * Y) + (2 : ℕ) • (Y * Y * Y) +
        Y * Y * Y * Y := by rw [heY]; noncomm_ring
    rw [this, hY3, one_mul, heY]
    module
  have hcXY : Commute X Y := hXY
  have hX_eY : Commute X eY := ((Commute.one_right X).add_right hcXY).add_right (hcXY.mul_right hcXY)
  have hXX_eY : Commute (X * X) eY := hX_eY.mul_left hX_eY
  have hc : Commute eX eY := ((Commute.one_left eY).add_left hX_eY).add_left hXX_eY
  set F : Matrix (Fin 3) (Fin 3) K := eX * eY with hF
  have hFF : F * F = (9 : K) • F := by
    calc F * F = eX * (eY * eX) * eY := by rw [hF]; simp only [mul_assoc]
      _ = eX * (eX * eY) * eY := by rw [hc.eq]
      _ = (eX * eX) * (eY * eY) := by simp only [mul_assoc]
      _ = ((3 : ℕ) • eX) * ((3 : ℕ) • eY) := by rw [hXX, hYY]
      _ = (9 : K) • F := by
        rw [smul_mul_smul_comm, hF, show (3 * 3 : ℕ) = 9 from rfl,
          show (9 : K) • (eX * eY) = (9 : ℕ) • (eX * eY) by
            rw [← Nat.cast_smul_eq_nsmul K]; norm_num]
  have htrF : F.trace = 3 := by
    rw [hF, heX, heY]
    simp only [add_mul, mul_add, mul_one, one_mul, Matrix.trace_add, t1, t2, t3, t4, t5, t6, t7,
      t8]
    simp
  have hidem : ((9 : K)⁻¹ • F) * ((9 : K)⁻¹ • F) = (9 : K)⁻¹ • F := by
    rw [smul_mul_smul_comm, hFF, smul_smul]
    congr 1
    field_simp
  obtain ⟨r, hr3, hr⟩ := trace_idem _ hidem
  refine ⟨r, hr3, ?_⟩
  rw [Matrix.trace_smul, htrF, smul_eq_mul] at hr
  field_simp at hr
  linear_combination -hr

end CFSG.RankThree.PartOne.A6N
