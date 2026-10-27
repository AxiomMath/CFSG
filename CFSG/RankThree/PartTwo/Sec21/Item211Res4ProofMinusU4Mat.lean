module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusL4Tools
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.LieType.Universal.Unitary (conjTr antidiag)

namespace Item211Res4Proof

open Item228Census3Proof Item228Census5Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def cstar {n : Type} (M : Matrix n n K) : Matrix n n K :=
  (M.map σ)ᵀ

theorem cstar_mul {n : Type} [Fintype n] (M N : Matrix n n K) :
    cstar σ (M * N) = cstar σ N * cstar σ M := by
  simp only [cstar, Matrix.map_mul, transpose_mul]

theorem cstar_one {n : Type} [DecidableEq n] : cstar σ (1 : Matrix n n K) = 1 := by
  rw [cstar, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem cstar_fromBlocks (A B C D : Matrix (Fin 2) (Fin 2) K) :
    cstar σ (fromBlocks A B C D) = fromBlocks (cstar σ A) (cstar σ C) (cstar σ B) (cstar σ D) := by
  rw [cstar, fromBlocks_map, fromBlocks_transpose]
  rfl

theorem cstar_zero : cstar σ (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j
  simp [cstar]

theorem cstar_smul (c : K) (M : Matrix (Fin 2) (Fin 2) K) :
    cstar σ (c • M) = σ c • cstar σ M := by
  ext i j
  simp [cstar]

theorem cstar_eq_transpose {M : Matrix (Fin 2) (Fin 2) K} (hM : M.map σ = M) :
    cstar σ M = Mᵀ := by
  rw [cstar, hM]

@[expose] def jMat : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, 0]

@[expose] def dMat : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

@[expose] def jTwo : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem transpose_mul_jMat_mul (M : Matrix (Fin 2) (Fin 2) K) :
    Mᵀ * jMat * M = M.det • jMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem jMat_mul_dMat : (jMat : Matrix (Fin 2) (Fin 2) K) * dMat = jTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, dMat, jTwo, Matrix.mul_apply, Fin.sum_univ_two]

theorem dMat_mul_jMat : (dMat : Matrix (Fin 2) (Fin 2) K) * jMat = -jTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, dMat, jTwo, Matrix.mul_apply, Fin.sum_univ_two]

theorem dMat_mul_dMat : (dMat : Matrix (Fin 2) (Fin 2) K) * dMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem map_dMat : (dMat : Matrix (Fin 2) (Fin 2) K).map σ = dMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat]

theorem transpose_dMat : (dMat : Matrix (Fin 2) (Fin 2) K)ᵀ = dMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat]

theorem det_map_two (M : Matrix (Fin 2) (Fin 2) K) : (M.map σ).det = σ M.det := by
  simp [Matrix.det_fin_two]

theorem map_mul_equiv {n : Type} [Fintype n] (M N : Matrix n n K) :
    (M * N).map σ = M.map σ * N.map σ := by
  ext i j
  simp [Matrix.mul_apply, map_sum]

theorem map_map_of_invol (hσ : ∀ c, σ (σ c) = c) (M : Matrix (Fin 2) (Fin 2) K) :
    (M.map σ).map σ = M := by
  ext i j
  simp [hσ]

theorem map_eq_of_cstar_jMat {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (h : cstar σ M * jMat * M = jMat) : M.map σ = M := by
  have h1 : Mᵀ * jMat * M = jMat := by rw [transpose_mul_jMat_mul, hdet, one_smul]
  have hinv : IsUnit (jMat * M) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hdet, mul_one]
    simp [jMat, Matrix.det_fin_two]
  have h2 : cstar σ M = Mᵀ := by
    have e : cstar σ M * (jMat * M) = Mᵀ * (jMat * M) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
    exact (hinv.mul_left_inj).mp e
  have h3 := congrArg Matrix.transpose h2
  rw [cstar, transpose_transpose, transpose_transpose] at h3
  exact h3

@[expose] def formV : Matrix V₄ V₄ K := fromBlocks 0 jTwo jTwo 0

@[expose] def formQ : Matrix V₄ V₄ K := fromBlocks 0 jMat (-jMat) 0

theorem submatrix_antidiag :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K).submatrix idxV₄ idxV₄ = formV := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [antidiag, formV, jTwo, idxV₄, Fin.rev] <;> decide

theorem idxV₄_inl_zero : idxV₄ (Sum.inl 0 : V₄) = 0 := rfl

theorem idxV₄_inl_one : idxV₄ (Sum.inl 1 : V₄) = 1 := rfl

theorem idxV₄_inr_zero : idxV₄ (Sum.inr 0 : V₄) = 2 := rfl

theorem idxV₄_inr_one : idxV₄ (Sum.inr 1 : V₄) = 3 := rfl

theorem dMat_map_dMat (B : Matrix (Fin 2) (Fin 2) K) :
    dMat * B.map σ * dMat = !![σ (B 0 0), -σ (B 0 1); -σ (B 1 0), σ (B 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem submatrix_blkSo (B : Matrix (Fin 2) (Fin 2) K) :
    (blkSo σ B).submatrix idxV₄ idxV₄ = fromBlocks B 0 0 (dMat * B.map σ * dMat) := by
  rw [dMat_map_dMat]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [blkSo, idxV₄_inl_zero, idxV₄_inl_one, idxV₄_inr_zero, idxV₄_inr_one]

theorem submatrix_conjTr (M : Matrix (Fin 4) (Fin 4) K) :
    (conjTr σ M).submatrix idxV₄ idxV₄ = cstar σ (M.submatrix idxV₄ idxV₄) :=
  rfl

theorem mem_SU_iff_blocks (g : GL (Fin 4) K) :
    g ∈ CFSG.LieType.Universal.Unitary.SU σ 4 ↔ (g : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      cstar σ ((g : Matrix (Fin 4) (Fin 4) K).submatrix idxV₄ idxV₄) * formV *
        (g : Matrix (Fin 4) (Fin 4) K).submatrix idxV₄ idxV₄ = formV := by
  rw [CFSG.LieType.Universal.Unitary.mem_SU]
  refine and_congr_right fun _ => ?_
  rw [← submatrix_conjTr, ← submatrix_antidiag, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  constructor
  · intro h
    rw [h]
  · intro h
    have e := congrArg (fun M : Matrix V₄ V₄ K => M.submatrix idxV₄.symm idxV₄.symm) h
    simpa [Matrix.submatrix_submatrix] using e

@[expose] def piMat : Matrix V₄ V₄ K :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 1, 0] !![0, 1; 0, 0] !![0, 0; 0, 1]

theorem piMat_mul_self : (piMat : Matrix V₄ V₄ K) * piMat = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [piMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem cstar_piMat : cstar σ (piMat : Matrix V₄ V₄ K) = piMat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [piMat, cstar]

theorem piMat_formQ : (piMat : Matrix V₄ V₄ K) * formQ * piMat = formQ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [piMat, formQ, jMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem piMat_conj_blk (M : Matrix (Fin 2) (Fin 2) K) :
    piMat * fromBlocks M 0 0 M * piMat =
      fromBlocks (M 0 0 • 1) (M 0 1 • 1) (M 1 0 • 1) (M 1 1 • 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [piMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem piMat_conj_scalar (x y : K) :
    piMat * fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) * piMat =
      fromBlocks !![x, 0; 0, y] 0 0 !![x, 0; 0, y] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [piMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply]

@[expose] def zOne (PR : Matrix (Fin 2) (Fin 2) K) (l : K) : Matrix V₄ V₄ K :=
  fromBlocks PR 0 0 (l • (PR.map σ * dMat))

@[expose] def zOneInv (PiR : Matrix (Fin 2) (Fin 2) K) (l : K) : Matrix V₄ V₄ K :=
  fromBlocks PiR 0 0 (l⁻¹ • (dMat * PiR.map σ))

@[expose] def zMat (PR : Matrix (Fin 2) (Fin 2) K) (l : K) : Matrix V₄ V₄ K :=
  piMat * zOne σ PR l

@[expose] def zMatInv (PiR : Matrix (Fin 2) (Fin 2) K) (l : K) : Matrix V₄ V₄ K :=
  zOneInv σ PiR l * piMat

variable {σ}

theorem zOne_mul_zOneInv {PR PiR : Matrix (Fin 2) (Fin 2) K} (h : PR * PiR = 1) {l : K}
    (hl : l ≠ 0) : zOne σ PR l * zOneInv σ PiR l = 1 := by
  have e : l • (PR.map σ * dMat) * (l⁻¹ • (dMat * PiR.map σ)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl, one_smul,
      Matrix.mul_assoc, ← Matrix.mul_assoc dMat, dMat_mul_dMat, Matrix.one_mul, ← map_mul_equiv,
      h, Matrix.map_one _ (map_zero σ) (map_one σ)]
  rw [zOne, zOneInv, fromBlocks_multiply, ← fromBlocks_one, h, e]
  simp

theorem zOneInv_mul_zOne {PR PiR : Matrix (Fin 2) (Fin 2) K} (h : PiR * PR = 1) {l : K}
    (hl : l ≠ 0) : zOneInv σ PiR l * zOne σ PR l = 1 := by
  have e : l⁻¹ • (dMat * PiR.map σ) * (l • (PR.map σ * dMat)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl, one_smul,
      Matrix.mul_assoc, ← Matrix.mul_assoc (PiR.map σ), ← map_mul_equiv, h,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, dMat_mul_dMat]
  rw [zOne, zOneInv, fromBlocks_multiply, ← fromBlocks_one, h, e]
  simp

theorem zMat_mul_zMatInv {PR PiR : Matrix (Fin 2) (Fin 2) K} (h : PR * PiR = 1) {l : K}
    (hl : l ≠ 0) : zMat σ PR l * zMatInv σ PiR l = 1 := by
  rw [zMat, zMatInv, Matrix.mul_assoc, ← Matrix.mul_assoc (zOne σ PR l), zOne_mul_zOneInv h hl,
    Matrix.one_mul, piMat_mul_self]

theorem zMatInv_mul_zMat {PR PiR : Matrix (Fin 2) (Fin 2) K} (h : PiR * PR = 1) {l : K}
    (hl : l ≠ 0) : zMatInv σ PiR l * zMat σ PR l = 1 := by
  rw [zMat, zMatInv, Matrix.mul_assoc, ← Matrix.mul_assoc piMat, piMat_mul_self, Matrix.one_mul,
    zOneInv_mul_zOne h hl]

theorem cstar_zMat_formQ (hσ : ∀ c, σ (σ c) = c) {PR PiR : Matrix (Fin 2) (Fin 2) K}
    (h : PR * PiR = 1) :
    cstar σ (zMat σ PR (σ PiR.det)) * formQ * zMat σ PR (σ PiR.det) = formV := by
  have hdet : PR.det * PiR.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have hPi : cstar σ (zMat σ PR (σ PiR.det)) * formQ * zMat σ PR (σ PiR.det) =
      cstar σ (zOne σ PR (σ PiR.det)) * formQ * zOne σ PR (σ PiR.det) := by
    rw [zMat, cstar_mul, cstar_piMat]
    calc cstar σ (zOne σ PR (σ PiR.det)) * piMat * formQ * (piMat * zOne σ PR (σ PiR.det)) =
        cstar σ (zOne σ PR (σ PiR.det)) * (piMat * formQ * piMat) * zOne σ PR (σ PiR.det) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [piMat_formQ]
  rw [hPi, zOne, cstar_fromBlocks, cstar_zero, cstar_smul, formQ, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have e1 : cstar σ PR * jMat * (σ PiR.det • (PR.map σ * dMat)) = jTwo := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, cstar, transpose_mul_jMat_mul, det_map_two,
      Matrix.smul_mul, jMat_mul_dMat, smul_smul, ← map_mul, mul_comm, hdet, map_one, one_smul]
  have hc : cstar σ (PR.map σ * dMat) = dMat * PRᵀ := by
    rw [cstar_mul, cstar, cstar, map_dMat, transpose_dMat, map_map_of_invol σ hσ]
  have e2 : σ (σ PiR.det) • cstar σ (PR.map σ * dMat) * -jMat * PR = jTwo := by
    rw [hσ, hc]
    simp only [Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PRᵀ jMat PR, transpose_mul_jMat_mul, Matrix.mul_smul, dMat_mul_jMat]
    simp only [smul_neg, neg_neg, smul_smul]
    rw [mul_comm, hdet, one_smul]
  rw [e1, e2, formV]

theorem zMat_conj_blkSo {PR PiR U q₀ : Matrix (Fin 2) (Fin 2) K} (hU : PR * U * PiR = q₀)
    (hq : q₀.map σ = q₀) {l : K} (hl : l ≠ 0) :
    zMat σ PR l * fromBlocks U 0 0 (dMat * U.map σ * dMat) * zMatInv σ PiR l =
      fromBlocks (q₀ 0 0 • 1) (q₀ 0 1 • 1) (q₀ 1 0 • 1) (q₀ 1 1 • 1) := by
  have e : zOne σ PR l * fromBlocks U 0 0 (dMat * U.map σ * dMat) * zOneInv σ PiR l =
      fromBlocks q₀ 0 0 q₀ := by
    have eD : l • (PR.map σ * dMat) * (dMat * U.map σ * dMat) * (l⁻¹ • (dMat * PiR.map σ)) =
        q₀ := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl,
        one_smul]
      calc PR.map σ * dMat * (dMat * U.map σ * dMat) * (dMat * PiR.map σ) =
          PR.map σ * (dMat * dMat) * U.map σ * (dMat * dMat) * PiR.map σ := by
            simp only [Matrix.mul_assoc]
        _ = (PR * U * PiR).map σ := by
            rw [dMat_mul_dMat, Matrix.mul_one, Matrix.mul_one, map_mul_equiv, map_mul_equiv]
        _ = q₀ := by rw [hU, hq]
    rw [zOne, zOneInv, fromBlocks_multiply, fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨by simpa using hU, by simp, by simp, ?_⟩
    simpa using eD
  rw [zMat, zMatInv, ← piMat_conj_blk, ← e]
  simp only [Matrix.mul_assoc]

theorem zMat_conj_diag {PR PiR : Matrix (Fin 2) (Fin 2) K} (h : PR * PiR = 1) {l : K}
    (hl : l ≠ 0) (x y : K) :
    zMat σ PR l * fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) * zMatInv σ PiR l =
      fromBlocks !![x, 0; 0, y] 0 0 !![x, 0; 0, y] := by
  have hc : fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) * zOneInv σ PiR l =
      zOneInv σ PiR l * fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) := by
    rw [zOneInv, fromBlocks_multiply, fromBlocks_multiply]
    simp [smul_smul, mul_comm]
  have e : zOne σ PR l * fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) *
      zOneInv σ PiR l = fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) := by
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, zOne_mul_zOneInv h hl, Matrix.one_mul]
  rw [zMat, zMatInv, ← piMat_conj_scalar]
  calc piMat * zOne σ PR l * fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) *
      (zOneInv σ PiR l * piMat) = piMat * (zOne σ PR l *
        fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) * zOneInv σ PiR l) * piMat :=
        by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e]

theorem cstar_blk_formQ (Y : Matrix (Fin 2) (Fin 2) K) :
    cstar σ (fromBlocks Y 0 0 Y) * formQ * fromBlocks Y 0 0 Y =
      fromBlocks 0 (cstar σ Y * jMat * Y) (-(cstar σ Y * jMat * Y)) 0 := by
  rw [cstar_fromBlocks, cstar_zero, formQ, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero]

theorem cstar_blk_formQ_of_fixed {B : Matrix (Fin 2) (Fin 2) K} (hB : B.map σ = B)
    (hdet : B.det = 1) :
    cstar σ (fromBlocks B 0 0 B) * formQ * fromBlocks B 0 0 B = formQ := by
  rw [cstar_blk_formQ, cstar_eq_transpose σ hB, transpose_mul_jMat_mul, hdet, one_smul, formQ]

theorem cstar_jMat_of_blk {Y : Matrix (Fin 2) (Fin 2) K}
    (h : cstar σ (fromBlocks Y 0 0 Y) * formQ * fromBlocks Y 0 0 Y = formQ) :
    cstar σ Y * jMat * Y = jMat := by
  rw [cstar_blk_formQ, formQ] at h
  exact (Matrix.fromBlocks_inj.mp h).2.1

theorem cstar_conj_iff {n : Type} [Fintype n] [DecidableEq n] {Zm Zim F F' : Matrix n n K}
    (hZ : cstar σ Zm * F' * Zm = F) (h1 : Zm * Zim = 1) (h2 : Zim * Zm = 1)
    (h : Matrix n n K) :
    cstar σ h * F * h = F ↔ cstar σ (Zm * h * Zim) * F' * (Zm * h * Zim) = F' := by
  have hc : cstar σ Zim * cstar σ Zm = 1 := by rw [← cstar_mul, h1, cstar_one]
  have hc' : cstar σ Zm * cstar σ Zim = 1 := by rw [← cstar_mul, h2, cstar_one]
  constructor
  · intro hh
    calc cstar σ (Zm * h * Zim) * F' * (Zm * h * Zim)
        = cstar σ Zim * (cstar σ h * (cstar σ Zm * F' * Zm) * h) * Zim := by
          simp only [cstar_mul, Matrix.mul_assoc]
      _ = cstar σ Zim * (cstar σ Zm * F' * Zm) * Zim := by rw [hZ, hh]
      _ = (cstar σ Zim * cstar σ Zm) * F' * (Zm * Zim) := by simp only [Matrix.mul_assoc]
      _ = F' := by rw [hc, h1, Matrix.one_mul, Matrix.mul_one]
  · intro hh
    have hW : Zm * h = Zm * h * Zim * Zm := by rw [Matrix.mul_assoc (Zm * h), h2, Matrix.mul_one]
    calc cstar σ h * F * h = cstar σ (Zm * h) * F' * (Zm * h) := by
          rw [← hZ, cstar_mul]
          simp only [Matrix.mul_assoc]
      _ = cstar σ (Zm * h * Zim * Zm) * F' * (Zm * h * Zim * Zm) := by rw [← hW]
      _ = cstar σ Zm * (cstar σ (Zm * h * Zim) * F' * (Zm * h * Zim)) * Zm := by
          rw [cstar_mul σ (Zm * h * Zim) Zm]
          simp only [Matrix.mul_assoc]
      _ = F := by rw [hh, hZ]

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
