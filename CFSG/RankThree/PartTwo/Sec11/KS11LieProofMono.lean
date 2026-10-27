module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank
open Matrix

theorem pow_conj_eq_of_conj_eq {M : Type*} [Group M] {m d z : M} (hz : Commute z m)
    (h : m * d * m⁻¹ = z * d) (n : ℕ) : m ^ n * d * (m ^ n)⁻¹ = z ^ n * d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : Commute (z ^ n) m := hz.pow_left n
    calc m ^ (n + 1) * d * (m ^ (n + 1))⁻¹ = m * (m ^ n * d * (m ^ n)⁻¹) * m⁻¹ := by
          rw [pow_succ']
          group
      _ = z ^ n * (m * d * m⁻¹) := by
          rw [ih, ← mul_assoc, ← hzn.eq]
          group
      _ = z ^ (n + 1) * d := by rw [h, pow_succ, mul_assoc]

variable {K : Type} [Field K]

theorem blockMat_add (a a' : K) (B B' : Matrix (Fin 2) (Fin 2) K) :
    blockMat a B + blockMat a' B' = blockMat (a + a') (B + B') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockMat_one_zero_mul_mul (X : Matrix (Fin 3) (Fin 3) K) :
    blockMat 1 (0 : Matrix (Fin 2) (Fin 2) K) * X * blockMat 1 0 = X 0 0 • blockMat 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem blockMat_one_zero_mul_self :
    blockMat 1 (0 : Matrix (Fin 2) (Fin 2) K) * blockMat 1 0 = blockMat 1 0 := by
  rw [blockMat_mul, one_mul, Matrix.mul_zero]

theorem coe_diagE_eq_add (e : Kˣ) :
    ((diagE e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 + ((e : K) - 1) • blockMat 1 (0 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem one_add_add_mul_self_eq_zero {B : GL (Fin 2) K} (hBdet : GeneralLinearGroup.det B = 1)
    (h3 : (3 : K) ≠ 0) (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    1 + (B : Matrix (Fin 2) (Fin 2) K) + (B : Matrix (Fin 2) (Fin 2) K) * B = 0 := by
  have h3' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast h3
  have hdet := det_sub_one_ne_zero (matDet_eq_one hBdet) h3' hB3 hB1
  have hBm3 : (B : Matrix (Fin 2) (Fin 2) K) * B * B = 1 := by
    have := congrArg Units.val hB3
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, sq] at this
    exact this
  have hprod : ((B : Matrix (Fin 2) (Fin 2) K) - 1) *
      (1 + (B : Matrix (Fin 2) (Fin 2) K) + (B : Matrix (Fin 2) (Fin 2) K) * B) = 0 := by
    have e : ((B : Matrix (Fin 2) (Fin 2) K) - 1) *
        (1 + (B : Matrix (Fin 2) (Fin 2) K) + (B : Matrix (Fin 2) (Fin 2) K) * B) =
        (B : Matrix (Fin 2) (Fin 2) K) * B * B - 1 := by noncomm_ring
    rw [e, hBm3, sub_self]
  have hunit : IsUnit ((B : Matrix (Fin 2) (Fin 2) K) - 1).det := isUnit_iff_ne_zero.mpr hdet
  have := congrArg (((B : Matrix (Fin 2) (Fin 2) K) - 1)⁻¹ * ·) hprod
  simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit] using this

theorem one_add_add_blockMat {Bm : Matrix (Fin 2) (Fin 2) K} (hB : 1 + Bm + Bm * Bm = 0) :
    1 + blockMat 1 Bm + blockMat 1 Bm * blockMat 1 Bm =
      (3 : K) • blockMat 1 (0 : Matrix (Fin 2) (Fin 2) K) := by
  rw [blockMat_mul, ← blockMat_one, blockMat_add, blockMat_add, blockMat_smul, hB, smul_zero]
  congr 1
  norm_num

theorem commute_diagE_of_commute_blockHom {B : GL (Fin 2) K}
    (hBdet : GeneralLinearGroup.det B = 1) (h3 : (3 : K) ≠ 0) (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1)
    {M : GL (Fin 3) K} (hM : M * blockHom B = blockHom B * M) (e : Kˣ) :
    M * diagE e = diagE e * M := by
  set Δ := blockMat (1 : K) (B : Matrix (Fin 2) (Fin 2) K) with hΔ
  set E₀ := blockMat (1 : K) (0 : Matrix (Fin 2) (Fin 2) K) with hE₀
  set Mm := (M : Matrix (Fin 3) (Fin 3) K) with hMm
  have hMΔ : Mm * Δ = Δ * Mm := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hM
    simpa only [Units.val_mul, coe_blockHom_of_det hBdet] using this
  have hF : 1 + Δ + Δ * Δ = (3 : K) • E₀ :=
    one_add_add_blockMat (one_add_add_mul_self_eq_zero hBdet h3 hB3 hB1)
  have hMΔ2 : Mm * (Δ * Δ) = Δ * Δ * Mm := by
    rw [← Matrix.mul_assoc, hMΔ, Matrix.mul_assoc, hMΔ, ← Matrix.mul_assoc]
  have hME : Mm * E₀ = E₀ * Mm := by
    have h1 : Mm * (1 + Δ + Δ * Δ) = (1 + Δ + Δ * Δ) * Mm := by
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul, hMΔ, hMΔ2]
    rw [hF, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ h3 h1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE_eq_add, ← hE₀, ← hMm, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hME]

theorem eq_smul_one_of_mul_eq_smul {T F F₁ F₂ : Matrix (Fin 3) (Fin 3) K} {t : K}
    (h3 : (3 : K) ≠ 0) (hsum : F + F₁ + F₂ = (3 : K) • 1) (h0 : T * F = t • F)
    (h1 : T * F₁ = t • F₁) (h2 : T * F₂ = t • F₂) : T = t • 1 := by
  have h : (3 : K) • T = (3 : K) • (t • (1 : Matrix (Fin 3) (Fin 3) K)) := by
    calc (3 : K) • T = T * ((3 : K) • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = T * (F + F₁ + F₂) := by rw [hsum]
      _ = T * F + T * F₁ + T * F₂ := by rw [Matrix.mul_add, Matrix.mul_add]
      _ = t • (F + F₁ + F₂) := by rw [h0, h1, h2, smul_add, smul_add]
      _ = (3 : K) • (t • 1) := by rw [hsum, smul_comm]
  exact smul_right_injective _ h3 h

theorem pow_three_mem_statedScalars_of_conj {B : GL (Fin 2) K}
    (hBdet : GeneralLinearGroup.det B = 1) (h3 : (3 : K) ≠ 0) (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1)
    {M : GL (Fin 3) K} {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hM : M * blockHom B * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * blockHom B) :
    M ^ 3 ∈ StatedScalars (Fin 3) K := by
  set Δ := blockMat (1 : K) (B : Matrix (Fin 2) (Fin 2) K) with hΔ
  set E₀ := blockMat (1 : K) (0 : Matrix (Fin 2) (Fin 2) K) with hE₀
  set Mm := (M : Matrix (Fin 3) (Fin 3) K) with hMm
  set Mi := ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hMi
  set z := (ζ : K) with hz
  have hMMi : Mm * Mi = 1 := by rw [hMm, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * Mm = 1 := by rw [hMm, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconj : Mm * Δ * Mi = z • Δ := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hM
    simp only [Units.val_mul, coe_blockHom_of_det hBdet, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hdetconj : ∀ X : Matrix (Fin 3) (Fin 3) K, (Mm * X * Mi).det = X.det := by
    intro X
    rw [det_mul, det_mul, mul_comm Mm.det, mul_assoc, ← det_mul, hMMi, det_one, mul_one]
  have hΔdet : Δ.det = 1 := by rw [hΔ, det_blockMat, matDet_eq_one hBdet, one_mul]
  have hz3 : z ^ 3 = 1 := by
    have h1 := hdetconj Δ
    rw [hconj, Matrix.det_smul, Fintype.card_fin, hΔdet, mul_one] at h1
    exact h1
  have hz1 : z ≠ 1 := fun h => hζ1 (Units.ext h)
  have hzz : 1 + z + z ^ 2 = 0 := by
    have h1 : (z - 1) * (1 + z + z ^ 2) = 0 := by linear_combination hz3
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hz1
    · exact h
  have hconjmul : ∀ X Y : Matrix (Fin 3) (Fin 3) K,
      Mm * (X * Y) * Mi = (Mm * X * Mi) * (Mm * Y * Mi) := by
    intro X Y
    calc Mm * (X * Y) * Mi = Mm * X * (Mi * Mm) * Y * Mi := by
          rw [hMiM, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (Mm * X * Mi) * (Mm * Y * Mi) := by simp only [Matrix.mul_assoc]
  have hconjadd : ∀ X Y : Matrix (Fin 3) (Fin 3) K,
      Mm * (X + Y) * Mi = Mm * X * Mi + Mm * Y * Mi := by
    intro X Y
    rw [Matrix.mul_add, Matrix.add_mul]
  have hconjsmul : ∀ (w : K) (X : Matrix (Fin 3) (Fin 3) K),
      Mm * (w • X) * Mi = w • (Mm * X * Mi) := by
    intro w X
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hconj1 : Mm * 1 * Mi = 1 := by rw [Matrix.mul_one, hMMi]
  have hconj2 : Mm * (Δ * Δ) * Mi = z ^ 2 • (Δ * Δ) := by
    rw [hconjmul, hconj, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  have hF : 1 + Δ + Δ * Δ = (3 : K) • E₀ :=
    one_add_add_blockMat (one_add_add_mul_self_eq_zero hBdet h3 hB3 hB1)
  have hF1 : Mm * (1 + Δ + Δ * Δ) * Mi = 1 + z • Δ + z ^ 2 • (Δ * Δ) := by
    rw [hconjadd, hconjadd, hconj1, hconj, hconj2]
  have hF2 : Mm * (Mm * (1 + Δ + Δ * Δ) * Mi) * Mi = 1 + z ^ 2 • Δ + z • (Δ * Δ) := by
    rw [hF1, hconjadd, hconjadd, hconj1, hconjsmul, hconjsmul, hconj, hconj2, smul_smul,
      smul_smul]
    have e1 : z * z = z ^ 2 := by ring
    have e2 : z ^ 2 * z ^ 2 = z := by linear_combination z * hz3
    rw [e1, e2]
  have hsum : (1 + Δ + Δ * Δ) + Mm * (1 + Δ + Δ * Δ) * Mi +
      Mm * (Mm * (1 + Δ + Δ * Δ) * Mi) * Mi = (3 : K) • 1 := by
    rw [hF2, hF1]
    have e : (1 + Δ + Δ * Δ) + (1 + z • Δ + z ^ 2 • (Δ * Δ)) + (1 + z ^ 2 • Δ + z • (Δ * Δ)) =
        (3 : K) • 1 + (1 + z + z ^ 2) • Δ + (1 + z + z ^ 2) • (Δ * Δ) := by module
    rw [e, hzz, zero_smul, zero_smul, add_zero, add_zero]
  set T := ((M ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hz3)
  have hTΔ : T * Δ = Δ * T := by
    have h1 := pow_conj_eq_of_conj_eq
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ M).symm hM 3
    rw [← map_pow, hζ3, map_one, one_mul] at h1
    have h2 : M ^ 3 * blockHom B = blockHom B * M ^ 3 := by
      calc M ^ 3 * blockHom B = (M ^ 3 * blockHom B * (M ^ 3)⁻¹) * M ^ 3 := by group
        _ = blockHom B * M ^ 3 := by rw [h1]
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) h2
    simpa only [Units.val_mul, coe_blockHom_of_det hBdet] using this
  have hTM : T * Mm = Mm * T := by
    rw [hT, hMm, ← Units.val_mul, ← Units.val_mul, ← pow_succ, ← pow_succ']
  have hTΔ2 : T * (Δ * Δ) = Δ * Δ * T := by
    rw [← Matrix.mul_assoc, hTΔ, Matrix.mul_assoc, hTΔ, ← Matrix.mul_assoc]
  have hTF : T * (1 + Δ + Δ * Δ) = (1 + Δ + Δ * Δ) * T := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hTΔ, hTΔ2]
  have hTE : T * E₀ = E₀ * T := by
    rw [hF, Matrix.mul_smul, Matrix.smul_mul] at hTF
    exact smul_right_injective _ h3 hTF
  have hEE : E₀ * E₀ = E₀ := blockMat_one_zero_mul_self
  have hETE : E₀ * T * E₀ = T 0 0 • E₀ := blockMat_one_zero_mul_mul T
  have hTE' : T * E₀ = T 0 0 • E₀ := by
    rw [← hETE, ← hTE, Matrix.mul_assoc, hEE]
  have hTF' : T * (1 + Δ + Δ * Δ) = T 0 0 • (1 + Δ + Δ * Δ) := by
    rw [hF, Matrix.mul_smul, hTE', smul_comm]
  have hTconj : ∀ X : Matrix (Fin 3) (Fin 3) K, T * X = T 0 0 • X →
      T * (Mm * X * Mi) = T 0 0 • (Mm * X * Mi) := by
    intro X hX
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTM, Matrix.mul_assoc Mm, hX, Matrix.mul_smul,
      Matrix.smul_mul]
  have hTF1 := hTconj _ hTF'
  have hTF2 := hTconj _ hTF1
  have hTeq : T = T 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) :=
    eq_smul_one_of_mul_eq_smul h3 hsum hTF' hTF1 hTF2
  refine mem_statedScalars_of_eq_smul hTeq fun h0 => ?_
  have hdet := congrArg Matrix.det hTeq
  rw [h0, zero_smul, det_zero] at hdet
  exact ((M ^ 3).isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero hdet

section Block

theorem eq_one_of_blockHom_mem_statedScalars {B : GL (Fin 2) K}
    (hB : GeneralLinearGroup.det B = 1)
    (h : blockHom B ∈ StatedScalars (Fin 3) K) : B = 1 := by
  obtain ⟨z, hz⟩ := h
  have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hz
  simp only [GeneralLinearGroup.coe_scalar, coe_blockHom_of_det hB] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e12 := congrFun (congrFun h1 1) 2
  have e21 := congrFun (congrFun h1 2) 1
  have e22 := congrFun (congrFun h1 2) 2
  simp [blockMat, Matrix.scalar_apply, Matrix.diagonal] at e00 e11 e12 e21 e22
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem conj_pow_gl {M : Type*} [Group M] (h D : M) (n : ℕ) :
    (h * D * h⁻¹) ^ n = h * D ^ n * h⁻¹ := by
  rw [← conj_pow]

end Block

section Scalars

theorem conj_mem_statedScalars_iff {h X : GL (Fin 3) K} :
    h * X * h⁻¹ ∈ StatedScalars (Fin 3) K ↔ X ∈ StatedScalars (Fin 3) K := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar z h).eq
    calc GeneralLinearGroup.scalar (Fin 3) z =
        h⁻¹ * (GeneralLinearGroup.scalar (Fin 3) z * h) := by rw [← hc]; group
      _ = X := by rw [hz]; group
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar z h).eq
    rw [← hz, hc]
    group

theorem diagE_pow (e : Kˣ) (n : ℕ) : diagE e ^ n = diagE (e ^ n) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagE, coe_diagE, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem eq_of_scalar_eq_diagE_mul_blockHom {e ζ : Kˣ} {B : GL (Fin 2) K}
    (hB : GeneralLinearGroup.det B = 1)
    (h : GeneralLinearGroup.scalar (Fin 3) ζ = diagE e * blockHom B) :
    (e : K) = ζ ∧ (B : Matrix (Fin 2) (Fin 2) K) = (ζ : K) • 1 := by
  have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h
  simp only [GeneralLinearGroup.coe_scalar, Units.val_mul, coe_diagE, coe_blockHom_of_det hB]
    at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e12 := congrFun (congrFun h1 1) 2
  have e21 := congrFun (congrFun h1 2) 1
  have e22 := congrFun (congrFun h1 2) 2
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul] at e00 e11 e12 e21 e22
  simp [blockMat] at e00 e11 e12 e21 e22
  refine ⟨e00.symm, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b
  · simp [← e11]
  · simp [← e12]
  · simp [← e21]
  · simp [← e22]

end Scalars

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
