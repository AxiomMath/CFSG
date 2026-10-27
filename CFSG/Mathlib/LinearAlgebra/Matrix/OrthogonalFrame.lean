module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NoncommRing

public section

namespace Matrix

variable {n : ℕ} {F : Type*} [Field F]

structure IsOrthogonalFrame (B P₁ P₂ S : Matrix (Fin n) (Fin n) F) : Prop where
  idem₁ : P₁ * P₁ = P₁
  idem₂ : P₂ * P₂ = P₂
  orth₁₂ : P₁ * P₂ = 0
  orth₂₁ : P₂ * P₁ = 0
  ne₁ : P₁ ≠ 0
  ne₂ : P₂ ≠ 0
  comm₁ : B * P₁ = P₁ * B
  comm₂ : B * P₂ = P₂ * B
  commS : B * S = S * B
  swap : S * S = 1
  swap₁ : S * P₁ = P₂ * S
  swap₂ : S * P₂ = P₁ * S

@[expose] def orthRotation (B P₁ P₂ : Matrix (Fin n) (Fin n) F) (lam ω : F) (j : ℕ) :
    Matrix (Fin n) (Fin n) F :=
  1 + (lam • B ^ j - 1) * P₁ + (ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₂

section Product

variable {P₁ P₂ a b a' b' : Matrix (Fin n) (Fin n) F}

private lemma cq1_pow_mul_pow {M : Type*} [Monoid M] {x y : M} (h : x * y = 1) (j : ℕ) :
    x ^ j * y ^ j = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (j + 1) * y ^ (j + 1) = x * (x ^ j * y ^ j) * y := by
      rw [pow_succ', pow_succ]
      simp only [mul_assoc]
    rw [e, ih, mul_one, h]

private lemma cq1_four_mul {R : Type*} [Ring R] (x y z w : R) :
    (x * y) * (z * w) = x * ((y * z) * w) := by noncomm_ring

private lemma cq1_sub_one_smul_mul {r : F} {P : Matrix (Fin n) (Fin n) F} :
    ((r • (1 : Matrix (Fin n) (Fin n) F) - 1) * P) = (r - 1) • P := by
  rw [sub_mul, one_mul, smul_mul_assoc, one_mul, sub_smul, one_smul]

private lemma cq1_eq_zero_of_smul_eq_zero {r : F} {P : Matrix (Fin n) (Fin n) F}
    (hP : P ≠ 0) (h : r • P = 0) : r = 0 := by
  by_contra hr
  obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
    by_contra h'
    exact hP (by ext i j; by_contra hij; exact h' ⟨i, j, hij⟩)
  have h' : r * P i j = 0 := by
    have := congrArg (fun M => M i j) h
    simpa [Matrix.smul_apply] using this
  exact hij ((mul_eq_zero.mp h').resolve_left hr)

private lemma cq1_mul_PP {R : Type*} [Ring R] {p a a' : R} (h : p * p = p)
    (ha : a' * p = p * a') : ((a - 1) * p) * ((a' - 1) * p) = (a - 1) * (a' - 1) * p := by
  have ha' : p * (a' - 1) = (a' - 1) * p := by
    rw [mul_sub, mul_one, sub_mul, one_mul, ha]
  calc ((a - 1) * p) * ((a' - 1) * p)
      = (a - 1) * ((p * (a' - 1)) * p) := cq1_four_mul (a - 1) p (a' - 1) p
    _ = (a - 1) * (((a' - 1) * p) * p) := by rw [ha']
    _ = (a - 1) * ((a' - 1) * (p * p)) := by rw [mul_assoc]
    _ = (a - 1) * ((a' - 1) * p) := by rw [h]
    _ = (a - 1) * (a' - 1) * p := by noncomm_ring

private lemma cq1_mul_PP_zero {R : Type*} [Ring R] {p₁ p₂ a b' : R} (h₁₂ : p₁ * p₂ = 0)
    (hb : b' * p₁ = p₁ * b') : ((a - 1) * p₁) * ((b' - 1) * p₂) = 0 := by
  have hb' : p₁ * (b' - 1) = (b' - 1) * p₁ := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hb]
  calc ((a - 1) * p₁) * ((b' - 1) * p₂)
      = (a - 1) * ((p₁ * (b' - 1)) * p₂) := cq1_four_mul (a - 1) p₁ (b' - 1) p₂
    _ = (a - 1) * (((b' - 1) * p₁) * p₂) := by rw [hb']
    _ = (a - 1) * ((b' - 1) * (p₁ * p₂)) := by rw [mul_assoc]
    _ = (a - 1) * ((b' - 1) * 0) := by rw [h₁₂]
    _ = 0 := by rw [mul_zero, mul_zero]

private lemma cq1_mul_PP_zero' {R : Type*} [Ring R] {p₁ p₂ b a' : R} (h₂₁ : p₂ * p₁ = 0)
    (ha : a' * p₂ = p₂ * a') : ((b - 1) * p₂) * ((a' - 1) * p₁) = 0 := by
  have ha' : p₂ * (a' - 1) = (a' - 1) * p₂ := by
    rw [mul_sub, mul_one, sub_mul, one_mul, ha]
  calc ((b - 1) * p₂) * ((a' - 1) * p₁)
      = (b - 1) * ((p₂ * (a' - 1)) * p₁) := cq1_four_mul (b - 1) p₂ (a' - 1) p₁
    _ = (b - 1) * (((a' - 1) * p₂) * p₁) := by rw [ha']
    _ = (b - 1) * ((a' - 1) * (p₂ * p₁)) := by rw [mul_assoc]
    _ = (b - 1) * ((a' - 1) * 0) := by rw [h₂₁]
    _ = 0 := by rw [mul_zero, mul_zero]

theorem rotation_mul (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂) (h₁₂ : P₁ * P₂ = 0)
    (h₂₁ : P₂ * P₁ = 0) (ha₁ : a' * P₁ = P₁ * a') (ha₂ : a' * P₂ = P₂ * a')
    (hb₁ : b' * P₁ = P₁ * b') (hb₂ : b' * P₂ = P₂ * b') :
    (1 + (a - 1) * P₁ + (b - 1) * P₂) * (1 + (a' - 1) * P₁ + (b' - 1) * P₂) =
      1 + (a * a' - 1) * P₁ + (b * b' - 1) * P₂ := by
  have hAA : ((a - 1) * P₁) * ((a' - 1) * P₁) = (a - 1) * (a' - 1) * P₁ :=
    cq1_mul_PP h₁ ha₁
  have hAB : ((a - 1) * P₁) * ((b' - 1) * P₂) = 0 := cq1_mul_PP_zero h₁₂ hb₁
  have hBA : ((b - 1) * P₂) * ((a' - 1) * P₁) = 0 := cq1_mul_PP_zero' h₂₁ ha₂
  have hBB : ((b - 1) * P₂) * ((b' - 1) * P₂) = (b - 1) * (b' - 1) * P₂ :=
    cq1_mul_PP h₂ hb₂
  simp only [mul_add, add_mul, one_mul, mul_one]
  rw [hAA, hAB, hBA, hBB]
  noncomm_ring

theorem rotation_pow (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂) (h₁₂ : P₁ * P₂ = 0)
    (h₂₁ : P₂ * P₁ = 0) (ha₁ : a * P₁ = P₁ * a) (ha₂ : a * P₂ = P₂ * a)
    (hb₁ : b * P₁ = P₁ * b) (hb₂ : b * P₂ = P₂ * b) (k : ℕ) :
    (1 + (a - 1) * P₁ + (b - 1) * P₂) ^ k = 1 + (a ^ k - 1) * P₁ + (b ^ k - 1) * P₂ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (1 + (a - 1) * P₁ + (b - 1) * P₂) ^ (k + 1)
        = (1 + (a - 1) * P₁ + (b - 1) * P₂) ^ k
            * (1 + (a - 1) * P₁ + (b - 1) * P₂) := by rw [pow_succ]
      _ = (1 + (a ^ k - 1) * P₁ + (b ^ k - 1) * P₂)
            * (1 + (a - 1) * P₁ + (b - 1) * P₂) := by rw [ih]
      _ = 1 + (a ^ k * a - 1) * P₁ + (b ^ k * b - 1) * P₂ :=
            rotation_mul h₁ h₂ h₁₂ h₂₁ ha₁ ha₂ hb₁ hb₂
      _ = 1 + (a ^ (k + 1) - 1) * P₁ + (b ^ (k + 1) - 1) * P₂ := by
            rw [pow_succ a k, pow_succ b k]

theorem smul_pow_cube_eq_smul_one {B : Matrix (Fin n) (Fin n) F} {c lam ω : F} {j : ℕ}
    (hB : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hlam : lam ^ 3 * c ^ j = ω) :
    (lam • B ^ j) ^ 3 = ω • (1 : Matrix (Fin n) (Fin n) F) := by
  calc (lam • B ^ j) ^ 3 = lam ^ 3 • (B ^ j) ^ 3 := by rw [smul_pow]
    _ = lam ^ 3 • B ^ (j * 3) := by rw [pow_mul]
    _ = lam ^ 3 • B ^ (3 * j) := by rw [Nat.mul_comm j 3]
    _ = lam ^ 3 • (B ^ 3) ^ j := by rw [← pow_mul B 3 j]
    _ = lam ^ 3 • (c • (1 : Matrix (Fin n) (Fin n) F)) ^ j := by rw [hB]
    _ = lam ^ 3 • (c ^ j • (1 : Matrix (Fin n) (Fin n) F)) := by rw [smul_pow, one_pow]
    _ = (lam ^ 3 * c ^ j) • (1 : Matrix (Fin n) (Fin n) F) := by rw [smul_smul]
    _ = ω • (1 : Matrix (Fin n) (Fin n) F) := by rw [hlam]

end Product

section Rotation

variable {B P₁ P₂ S : Matrix (Fin n) (Fin n) F} {c lam ω : F} {j : ℕ}

private lemma cq1_zeta_comm_P {B P : Matrix (Fin n) (Fin n) F} (h : Commute B P) (lam : F)
    (j : ℕ) : (lam • B ^ j) * P = P * (lam • B ^ j) :=
  ((h.pow_left j).smul_left lam).eq

private lemma cq1_zeta_comm_P' {B P : Matrix (Fin n) (Fin n) F} (h : Commute B P) (lam ω : F)
    (j : ℕ) : (ω⁻¹ • (lam • B ^ j) ^ 2) * P = P * (ω⁻¹ • (lam • B ^ j) ^ 2) :=
  ((((h.pow_left j).smul_left lam).pow_left 2).smul_left ω⁻¹).eq

private lemma cq1_comm_sub_one {p a : Matrix (Fin n) (Fin n) F} (ha : a * p = p * a) :
    (a - 1) * p = p * (a - 1) := by
  rw [sub_mul, one_mul, mul_sub, mul_one, ha]

private lemma cq1_det_sq {R S : Matrix (Fin n) (Fin n) F} (hSS : S * S = 1)
    (hRmul : R * (S * R * S) = 1) : R.det ^ 2 = 1 := by
  have hSd : S.det * S.det = 1 := by
    have h := congrArg Matrix.det hSS
    rwa [Matrix.det_mul, Matrix.det_one] at h
  have hdet : R.det * (S * R * S).det = 1 := by
    have h := congrArg Matrix.det hRmul
    rwa [Matrix.det_mul, Matrix.det_one] at h
  have hSRSdet : (S * R * S).det = R.det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_assoc, mul_comm R.det S.det,
        ← mul_assoc S.det S.det R.det, hSd, one_mul]
  rw [hSRSdet] at hdet
  rw [pow_two]
  exact hdet

private lemma cq1_conj_swap_P₁ {R : Type*} [Ring R] {ξ p₁ p₂ s : R} (hsξ : s * ξ = ξ * s)
    (hsp₁ : s * p₁ = p₂ * s) (hss : s * s = 1) :
    s * ((ξ - 1) * p₁) * s = (ξ - 1) * p₂ := by
  have hsξ' : s * (ξ - 1) = (ξ - 1) * s := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hsξ]
  calc s * ((ξ - 1) * p₁) * s
      = (s * (ξ - 1)) * p₁ * s := by noncomm_ring
    _ = ((ξ - 1) * s) * p₁ * s := by rw [hsξ']
    _ = (ξ - 1) * (s * p₁) * s := by noncomm_ring
    _ = (ξ - 1) * (p₂ * s) * s := by rw [hsp₁]
    _ = (ξ - 1) * p₂ * (s * s) := by noncomm_ring
    _ = (ξ - 1) * p₂ * 1 := by rw [hss]
    _ = (ξ - 1) * p₂ := by rw [mul_one]

private lemma cq1_conj_swap_P₂ {R : Type*} [Ring R] {ξ p₁ p₂ s : R} (hsξ : s * ξ = ξ * s)
    (hsp₂ : s * p₂ = p₁ * s) (hss : s * s = 1) :
    s * ((ξ - 1) * p₂) * s = (ξ - 1) * p₁ := by
  have hsξ' : s * (ξ - 1) = (ξ - 1) * s := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hsξ]
  calc s * ((ξ - 1) * p₂) * s
      = (s * (ξ - 1)) * p₂ * s := by noncomm_ring
    _ = ((ξ - 1) * s) * p₂ * s := by rw [hsξ']
    _ = (ξ - 1) * (s * p₂) * s := by noncomm_ring
    _ = (ξ - 1) * (p₁ * s) * s := by rw [hsp₂]
    _ = (ξ - 1) * p₁ * (s * s) := by noncomm_ring
    _ = (ξ - 1) * p₁ * 1 := by rw [hss]
    _ = (ξ - 1) * p₁ := by rw [mul_one]

private lemma cq1_adj_add (σ : F →+* F) (M N : Matrix (Fin n) (Fin n) F) :
    ((M + N).map σ)ᵀ = (M.map σ)ᵀ + (N.map σ)ᵀ := by
  rw [Matrix.map_add σ (map_add σ), Matrix.transpose_add]

private lemma cq1_adj_sub (σ : F →+* F) (M N : Matrix (Fin n) (Fin n) F) :
    ((M - N).map σ)ᵀ = (M.map σ)ᵀ - (N.map σ)ᵀ := by
  rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_sub]

private lemma cq1_adj_mul (σ : F →+* F) (M N : Matrix (Fin n) (Fin n) F) :
    ((M * N).map σ)ᵀ = (N.map σ)ᵀ * (M.map σ)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private lemma cq1_adj_one (σ : F →+* F) :
    (((1 : Matrix (Fin n) (Fin n) F).map σ)ᵀ) = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

private lemma cq1_adj_smul (σ : F →+* F) (r : F) (M : Matrix (Fin n) (Fin n) F) :
    ((r • M).map σ)ᵀ = σ r • (M.map σ)ᵀ := by
  rw [Matrix.map_smulₛₗ σ σ r (fun a => map_mul σ r a), Matrix.transpose_smul]

private lemma cq1_adj_pow (σ : F →+* F) (M : Matrix (Fin n) (Fin n) F) (j : ℕ) :
    ((M ^ j).map σ)ᵀ = ((M.map σ)ᵀ) ^ j := by
  rw [Matrix.map_pow, Matrix.transpose_pow]

private lemma cq1_smul_pow_commute {B P : Matrix (Fin n) (Fin n) F} (h : Commute B P) (r : F)
    (j : ℕ) : Commute (r • B ^ j) P := (h.pow_left j).smul_left r

theorem IsOrthogonalFrame.orthRotation_commute (hF : IsOrthogonalFrame B P₁ P₂ S) :
    orthRotation B P₁ P₂ lam ω j * B = B * orthRotation B P₁ P₂ lam ω j := by
  have hBζ : Commute B (lam • B ^ j) := ((Commute.refl B).pow_right j).smul_right lam
  have hBζ' : Commute B (ω⁻¹ • (lam • B ^ j) ^ 2) := (hBζ.pow_right 2).smul_right ω⁻¹
  have hBd₁ : Commute B (lam • B ^ j - 1) := hBζ.sub_right (Commute.one_right B)
  have hBd₂ : Commute B (ω⁻¹ • (lam • B ^ j) ^ 2 - 1) := hBζ'.sub_right (Commute.one_right B)
  have ht₁ : Commute B ((lam • B ^ j - 1) * P₁) := hBd₁.mul_right hF.comm₁
  have ht₂ : Commute B ((ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₂) := hBd₂.mul_right hF.comm₂
  have h := ((Commute.one_right B).add_right ht₁).add_right ht₂
  unfold orthRotation
  exact h.symm

theorem IsOrthogonalFrame.orthRotation_pow_nine (hF : IsOrthogonalFrame B P₁ P₂ S)
    (hB : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hlam : lam ^ 3 * c ^ j = ω)
    (hω : ω ^ 3 = 1) : orthRotation B P₁ P₂ lam ω j ^ 9 = 1 := by
  have hζP₁ := cq1_zeta_comm_P hF.comm₁ lam j
  have hζP₂ := cq1_zeta_comm_P hF.comm₂ lam j
  have hζ'P₁ := cq1_zeta_comm_P' hF.comm₁ lam ω j
  have hζ'P₂ := cq1_zeta_comm_P' hF.comm₂ lam ω j
  have hζ3 : (lam • B ^ j) ^ 3 = ω • (1 : Matrix (Fin n) (Fin n) F) :=
    smul_pow_cube_eq_smul_one hB hlam
  have hζ9 : (lam • B ^ j) ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hζ3, smul_pow, one_pow, hω, one_smul]
  have hω9 : ω ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hω, one_pow]
  have hζ'9 : (ω⁻¹ • (lam • B ^ j) ^ 2) ^ 9 = 1 := by
    rw [smul_pow, ← pow_mul (lam • B ^ j) 2 9, show 2 * 9 = 9 * 2 by norm_num,
        pow_mul (lam • B ^ j) 9 2, hζ9, one_pow, inv_pow, hω9, inv_one, one_smul]
  unfold orthRotation
  rw [rotation_pow hF.idem₁ hF.idem₂ hF.orth₁₂ hF.orth₂₁ hζP₁ hζP₂ hζ'P₁ hζ'P₂ 9, hζ9,
      hζ'9]
  simp

private lemma cq1_smul_comb_mul_P₁ {r s : F} {P₁ P₂ : Matrix (Fin n) (Fin n) F}
    (h₁ : P₁ * P₁ = P₁) (h₂₁ : P₂ * P₁ = 0) :
    (1 + (r - 1) • P₁ + (s - 1) • P₂) * P₁ = r • P₁ := by
  rw [add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂₁, smul_zero, add_zero]
  conv_rhs => rw [show r = 1 + (r - 1) by ring]
  rw [add_smul, one_smul]

private lemma cq1_smul_comb_mul_P₂ {r s : F} {P₁ P₂ : Matrix (Fin n) (Fin n) F}
    (h₁₂ : P₁ * P₂ = 0) (h₂ : P₂ * P₂ = P₂) :
    (1 + (r - 1) • P₁ + (s - 1) • P₂) * P₂ = s • P₂ := by
  rw [add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, h₁₂, h₂, smul_zero, add_zero]
  conv_rhs => rw [show s = 1 + (s - 1) by ring]
  rw [add_smul, one_smul]

private lemma cq1_eq_of_mul_eq {R : Matrix (Fin n) (Fin n) F} {r s : F}
    {P : Matrix (Fin n) (Fin n) F} (hP : P ≠ 0) (h₁ : R * P = r • P) (h₂ : R * P = s • P) :
    r = s := by
  have hz : (r - s) • P = 0 := by rw [sub_smul, ← h₁, h₂, sub_self]
  exact sub_eq_zero.mp (cq1_eq_zero_of_smul_eq_zero hP hz)

theorem IsOrthogonalFrame.orthRotation_pow_three_ne (hF : IsOrthogonalFrame B P₁ P₂ S)
    (hB : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hlam : lam ^ 3 * c ^ j = ω)
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (a : F) :
    orthRotation B P₁ P₂ lam ω j ^ 3 ≠ a • (1 : Matrix (Fin n) (Fin n) F) := by
  intro h
  have hζP₁ := cq1_zeta_comm_P hF.comm₁ lam j
  have hζP₂ := cq1_zeta_comm_P hF.comm₂ lam j
  have hζ'P₁ := cq1_zeta_comm_P' hF.comm₁ lam ω j
  have hζ'P₂ := cq1_zeta_comm_P' hF.comm₂ lam ω j
  have hζ3 : (lam • B ^ j) ^ 3 = ω • (1 : Matrix (Fin n) (Fin n) F) :=
    smul_pow_cube_eq_smul_one hB hlam
  have hζ'3 : (ω⁻¹ • (lam • B ^ j) ^ 2) ^ 3 = ω ^ 2 • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [smul_pow, ← pow_mul (lam • B ^ j) 2 3, show 2 * 3 = 3 * 2 by norm_num,
        pow_mul (lam • B ^ j) 3 2, hζ3, smul_pow, one_pow, smul_smul]
    congr 1
    rw [inv_pow, hω, inv_one, one_mul]
  have h3 : orthRotation B P₁ P₂ lam ω j ^ 3 = 1 + (ω - 1) • P₁ + (ω ^ 2 - 1) • P₂ := by
    unfold orthRotation
    rw [rotation_pow hF.idem₁ hF.idem₂ hF.orth₁₂ hF.orth₂₁ hζP₁ hζP₂ hζ'P₁ hζ'P₂ 3, hζ3,
        hζ'3, cq1_sub_one_smul_mul, cq1_sub_one_smul_mul]
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hω
    exact zero_ne_one hω
  have hP₁ : orthRotation B P₁ P₂ lam ω j ^ 3 * P₁ = ω • P₁ := by
    rw [h3, cq1_smul_comb_mul_P₁ hF.idem₁ hF.orth₂₁]
  have hP₁' : orthRotation B P₁ P₂ lam ω j ^ 3 * P₁ = a • P₁ := by
    rw [h, smul_mul_assoc, one_mul]
  have hωa : ω = a := cq1_eq_of_mul_eq hF.ne₁ hP₁ hP₁'
  have hP₂ : orthRotation B P₁ P₂ lam ω j ^ 3 * P₂ = ω ^ 2 • P₂ := by
    rw [h3, cq1_smul_comb_mul_P₂ hF.orth₁₂ hF.idem₂]
  have hP₂' : orthRotation B P₁ P₂ lam ω j ^ 3 * P₂ = a • P₂ := by
    rw [h, smul_mul_assoc, one_mul]
  have hω2a : ω ^ 2 = a := cq1_eq_of_mul_eq hF.ne₂ hP₂ hP₂'
  have hωeq : ω = ω ^ 2 := hωa.trans hω2a.symm
  have hsq : ω = ω * ω := by rw [← pow_two]; exact hωeq
  have h1ω : (1 : F) = ω := by
    apply mul_left_cancel₀ hω0
    rw [mul_one]
    exact hsq
  exact hω1 h1ω.symm

theorem IsOrthogonalFrame.orthRotation_det (hF : IsOrthogonalFrame B P₁ P₂ S)
    (hB : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hlam : lam ^ 3 * c ^ j = ω)
    (hω : ω ^ 3 = 1) : (orthRotation B P₁ P₂ lam ω j).det = 1 := by
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hω
    exact zero_ne_one hω
  have hζP₁ := cq1_zeta_comm_P hF.comm₁ lam j
  have hζP₂ := cq1_zeta_comm_P hF.comm₂ lam j
  have hζ'P₁ := cq1_zeta_comm_P' hF.comm₁ lam ω j
  have hζ'P₂ := cq1_zeta_comm_P' hF.comm₂ lam ω j
  have hζ3 : (lam • B ^ j) ^ 3 = ω • (1 : Matrix (Fin n) (Fin n) F) :=
    smul_pow_cube_eq_smul_one hB hlam
  have hSζ : Commute S (lam • B ^ j) :=
    (Commute.pow_right (Commute.symm hF.commS) j).smul_right lam
  have hSζ' : Commute S (ω⁻¹ • (lam • B ^ j) ^ 2) := (hSζ.pow_right 2).smul_right ω⁻¹
  have hSRS : S * orthRotation B P₁ P₂ lam ω j * S
      = 1 + (ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₁ + (lam • B ^ j - 1) * P₂ := by
    unfold orthRotation
    calc S * (1 + (lam • B ^ j - 1) * P₁ + (ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₂) * S
        = S * S + S * ((lam • B ^ j - 1) * P₁) * S
            + S * ((ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₂) * S := by noncomm_ring
      _ = 1 + (lam • B ^ j - 1) * P₂ + (ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₁ := by
            rw [hF.swap, cq1_conj_swap_P₁ hSζ hF.swap₁ hF.swap,
                cq1_conj_swap_P₂ hSζ' hF.swap₂ hF.swap]
      _ = 1 + (ω⁻¹ • (lam • B ^ j) ^ 2 - 1) * P₁ + (lam • B ^ j - 1) * P₂ := by
            noncomm_ring
  have hζζ' : (lam • B ^ j) * (ω⁻¹ • (lam • B ^ j) ^ 2) = 1 := by
    rw [mul_smul_comm, ← pow_succ' (lam • B ^ j) 2, hζ3, smul_smul, inv_mul_cancel₀ hω0,
        one_smul]
  have hζ'ζ : (ω⁻¹ • (lam • B ^ j) ^ 2) * (lam • B ^ j) = 1 := by
    rw [smul_mul_assoc, ← pow_succ (lam • B ^ j) 2, hζ3, smul_smul, inv_mul_cancel₀ hω0,
        one_smul]
  have hRmul : orthRotation B P₁ P₂ lam ω j *
      (S * orthRotation B P₁ P₂ lam ω j * S) = 1 := by
    rw [hSRS]
    unfold orthRotation
    rw [rotation_mul hF.idem₁ hF.idem₂ hF.orth₁₂ hF.orth₂₁ hζ'P₁ hζ'P₂ hζP₁ hζP₂]
    rw [hζζ', hζ'ζ]
    simp
  have hsq := cq1_det_sq hF.swap hRmul
  have h9 : (orthRotation B P₁ P₂ lam ω j).det ^ 9 = 1 := by
    have h := congrArg Matrix.det (IsOrthogonalFrame.orthRotation_pow_nine hF hB hlam hω)
    rwa [Matrix.det_pow, Matrix.det_one] at h
  have hD : (orthRotation B P₁ P₂ lam ω j).det ^ 9
      = (orthRotation B P₁ P₂ lam ω j).det := by
    rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, pow_add, pow_mul, hsq, one_pow, one_mul,
        pow_one]
  rw [← hD, h9]

private lemma cq1_adj_smul_pow (σ : F →+* F) (r : F) (B : Matrix (Fin n) (Fin n) F) (j : ℕ) :
    ((r • B ^ j).map σ)ᵀ = σ r • ((B.map σ)ᵀ) ^ j := by
  rw [cq1_adj_smul, cq1_adj_pow]

private lemma cq1_adj_smul_sq (σ : F →+* F) (r : F) (M : Matrix (Fin n) (Fin n) F) :
    ((r • M ^ 2).map σ)ᵀ = σ r • ((M.map σ)ᵀ) ^ 2 := by
  rw [cq1_adj_smul, cq1_adj_pow]

private lemma cq1_adj_orthRotation (hF : IsOrthogonalFrame B P₁ P₂ S) (σ : F →+* F)
    (hP₁ : (P₁.map σ)ᵀ = P₁) (hP₂ : (P₂.map σ)ᵀ = P₂) :
    ((orthRotation B P₁ P₂ lam ω j).map σ)ᵀ
      = 1 + (((lam • B ^ j).map σ)ᵀ - 1) * P₁
          + (((ω⁻¹ • (lam • B ^ j) ^ 2).map σ)ᵀ - 1) * P₂ := by
  have hBHP₁ : (B.map σ)ᵀ * P₁ = P₁ * (B.map σ)ᵀ := by
    have h := congrArg (fun M => (M.map σ)ᵀ) hF.comm₁
    simp only [Matrix.map_mul, Matrix.transpose_mul, hP₁] at h
    exact h.symm
  have hBHP₂ : (B.map σ)ᵀ * P₂ = P₂ * (B.map σ)ᵀ := by
    have h := congrArg (fun M => (M.map σ)ᵀ) hF.comm₂
    simp only [Matrix.map_mul, Matrix.transpose_mul, hP₂] at h
    exact h.symm
  have hζHP₁ : ((lam • B ^ j).map σ)ᵀ * P₁ = P₁ * ((lam • B ^ j).map σ)ᵀ := by
    rw [cq1_adj_smul_pow]
    exact (cq1_smul_pow_commute hBHP₁ (σ lam) j).eq
  have hζHP₂ : ((lam • B ^ j).map σ)ᵀ * P₂ = P₂ * ((lam • B ^ j).map σ)ᵀ := by
    rw [cq1_adj_smul_pow]
    exact (cq1_smul_pow_commute hBHP₂ (σ lam) j).eq
  have hζ'HP₁ : ((ω⁻¹ • (lam • B ^ j) ^ 2).map σ)ᵀ * P₁
      = P₁ * ((ω⁻¹ • (lam • B ^ j) ^ 2).map σ)ᵀ := by
    rw [cq1_adj_smul_sq, cq1_adj_smul_pow]
    exact (((cq1_smul_pow_commute hBHP₁ (σ lam) j).pow_left 2).smul_left (σ (ω⁻¹))).eq
  have hζ'HP₂ : ((ω⁻¹ • (lam • B ^ j) ^ 2).map σ)ᵀ * P₂
      = P₂ * ((ω⁻¹ • (lam • B ^ j) ^ 2).map σ)ᵀ := by
    rw [cq1_adj_smul_sq, cq1_adj_smul_pow]
    exact (((cq1_smul_pow_commute hBHP₂ (σ lam) j).pow_left 2).smul_left (σ (ω⁻¹))).eq
  unfold orthRotation
  simp only [cq1_adj_add, cq1_adj_sub, cq1_adj_mul, cq1_adj_one, hP₁, hP₂]
  rw [← cq1_comm_sub_one hζHP₁, ← cq1_comm_sub_one hζ'HP₂]

theorem IsOrthogonalFrame.orthRotation_unitary (hF : IsOrthogonalFrame B P₁ P₂ S) (σ : F →+* F)
    (hP₁ : (P₁.map σ)ᵀ = P₁) (hP₂ : (P₂.map σ)ᵀ = P₂) (hBu : (B.map σ)ᵀ * B = 1)
    (hlamσ : σ lam * lam = 1) (hωσ : σ ω * ω = 1) :
    ((orthRotation B P₁ P₂ lam ω j).map σ)ᵀ * orthRotation B P₁ P₂ lam ω j = 1 := by
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hωσ
    exact zero_ne_one hωσ
  have hσω : σ ω = ω⁻¹ := by
    have h := congrArg (fun x => x * ω⁻¹) hωσ
    simpa only [mul_assoc, mul_inv_cancel₀ hω0, mul_one, one_mul] using h
  have hσωinv : σ (ω⁻¹) * ω⁻¹ = 1 := by
    conv_lhs => enter [2]; rw [← hσω]
    rw [← map_mul σ (ω⁻¹) ω, inv_mul_cancel₀ hω0, map_one]
  have hζHζ : ((lam • B ^ j).map σ)ᵀ * (lam • B ^ j) = 1 := by
    rw [cq1_adj_smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul, cq1_pow_mul_pow hBu j,
        hlamσ, one_smul]
  have hζ'Hζ' : ((ω⁻¹ • (lam • B ^ j) ^ 2).map σ)ᵀ * (ω⁻¹ • (lam • B ^ j) ^ 2) = 1 := by
    rw [cq1_adj_smul_sq, smul_mul_assoc, mul_smul_comm, smul_smul, cq1_pow_mul_pow hζHζ 2,
        hσωinv, one_smul]
  rw [cq1_adj_orthRotation hF σ hP₁ hP₂]
  unfold orthRotation
  rw [rotation_mul hF.idem₁ hF.idem₂ hF.orth₁₂ hF.orth₂₁ (cq1_zeta_comm_P hF.comm₁ lam j)
      (cq1_zeta_comm_P hF.comm₂ lam j) (cq1_zeta_comm_P' hF.comm₁ lam ω j)
      (cq1_zeta_comm_P' hF.comm₂ lam ω j)]
  rw [hζHζ, hζ'Hζ']
  simp

end Rotation

end Matrix
