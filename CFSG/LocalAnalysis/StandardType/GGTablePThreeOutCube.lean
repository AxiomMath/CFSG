module

public import Mathlib

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix

private theorem smul_pow_mat {K : Type} [Field K] {n : ℕ} (c : K)
    (d : Matrix (Fin n) (Fin n) K) (k : ℕ) : (c • d) ^ k = c ^ k • d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, pow_succ]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm c (c ^ k)]

theorem outCube_of_conj {K : Type} [Field K] {q n : ℕ} (hn : 0 < n) (φ : K →+* K)
    (hφ : ∀ x, φ x = x ^ q) {d g : Matrix (Fin n) (Fin n) K} {lam c : K}
    (hlam : lam ^ (q + 1) = 1) (hd3 : d ^ 3 = lam • (1 : Matrix (Fin n) (Fin n) K))
    (hg : IsUnit g) (hconj : g * d.map φ * g⁻¹ = c • d) : ∃ μ : K, μ ^ 3 = lam := by
  obtain ⟨u, hu⟩ := hg
  rw [← hu] at hconj
  have hvalinv : (↑u : Matrix (Fin n) (Fin n) K)⁻¹ = ↑u⁻¹ :=
    Matrix.inv_eq_right_inv (Units.mul_inv u)
  rw [hvalinv] at hconj
  have hdmap3 : (d.map φ) ^ 3 = φ lam • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.map_pow d φ 3, hd3, Matrix.map_smul' (φ : K → K) lam 1 φ.map_mul,
      Matrix.map_one (φ : K → K) φ.map_zero φ.map_one]
  have hL : ((↑u : Matrix (Fin n) (Fin n) K) * d.map φ *
        (↑u⁻¹ : Matrix (Fin n) (Fin n) K)) ^ 3 =
      (↑u : Matrix (Fin n) (Fin n) K) * (d.map φ) ^ 3 *
        (↑u⁻¹ : Matrix (Fin n) (Fin n) K) :=
    Units.conj_pow u (d.map φ) 3
  have hcube : ((↑u : Matrix (Fin n) (Fin n) K) * d.map φ *
        (↑u⁻¹ : Matrix (Fin n) (Fin n) K)) ^ 3 = (c • d) ^ 3 := by
    rw [hconj]
  have hmain : (↑u : Matrix (Fin n) (Fin n) K) *
        (φ lam • (1 : Matrix (Fin n) (Fin n) K)) *
        (↑u⁻¹ : Matrix (Fin n) (Fin n) K) = (c • d) ^ 3 := by
    rw [← hdmap3]
    exact hL.symm.trans hcube
  have hleft : (↑u : Matrix (Fin n) (Fin n) K) *
        (φ lam • (1 : Matrix (Fin n) (Fin n) K)) *
        (↑u⁻¹ : Matrix (Fin n) (Fin n) K) =
        φ lam • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv u]
  have hright : (c • d) ^ 3 = (c ^ 3 * lam) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [smul_pow_mat c d 3, hd3, smul_smul]
  have hEq : φ lam • (1 : Matrix (Fin n) (Fin n) K) =
      (c ^ 3 * lam) • (1 : Matrix (Fin n) (Fin n) K) :=
    hleft.symm.trans (hmain.trans hright)
  let i : Fin n := ⟨0, hn⟩
  have hentry : φ lam = c ^ 3 * lam := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hEq
    simpa [Matrix.smul_apply, Matrix.one_apply_eq] using h
  have hlamq : lam ^ q = c ^ 3 * lam := by
    rw [← hφ lam]
    exact hentry
  have hc3 : c ^ 3 * lam ^ 2 = 1 := by
    have h : lam ^ q * lam = 1 := by
      rw [← pow_succ]
      exact hlam
    rw [hlamq] at h
    simpa [pow_two, mul_assoc] using h
  refine ⟨lam * c, ?_⟩
  calc (lam * c) ^ 3 = lam ^ 3 * c ^ 3 := by ring
    _ = lam * (lam ^ 2 * c ^ 3) := by ring
    _ = lam * (c ^ 3 * lam ^ 2) := by rw [mul_comm (lam ^ 2) (c ^ 3)]
    _ = lam * 1 := by rw [hc3]
    _ = lam := mul_one lam

end CFSG.StandardType.TablePThreeKG

end
