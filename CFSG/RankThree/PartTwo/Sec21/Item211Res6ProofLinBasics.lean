module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups

section Linear

variable {K : Type} [Field K]

theorem exists_scalar_of_conjAut_eq [Finite K] {A B : GL (Fin 3) K}
    (h : conjAut 3 K A = conjAut 3 K B) :
    ∃ c : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 3) c * B := by
  have h1 : conjAut 3 K (A * B⁻¹) * fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h1
  exact ⟨c, by rw [hc]; group⟩

theorem coe_scalar_three (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

theorem conjAut_mem_range_of_det {A : GL (Fin 3) K} {ν : K}
    (h : (A : Matrix (Fin 3) (Fin 3) K).det = ν ^ 3) :
    conjAut 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hν : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at h
    exact hdet h
  let g : SL(3, K) := ⟨ν⁻¹ • (A : Matrix (Fin 3) (Fin 3) K), by
    rw [Matrix.det_smul, h, Fintype.card_fin, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hν)]⟩
  refine ⟨proj 3 K g, ?_⟩
  rw [← conjAut_toGL]
  have hg : Matrix.SpecialLinearGroup.toGL g =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν)⁻¹ * A := by
    apply Units.ext
    rw [Units.val_mul, coe_scalar_three, Matrix.smul_mul, Matrix.one_mul]
    rfl
  rw [hg, map_mul, conjAut_scalar, one_mul]

theorem conjAut_mem_range_iff [Finite K] {A : GL (Fin 3) K} :
    conjAut 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ↔
      ∃ ν : K, (A : Matrix (Fin 3) (Fin 3) K).det = ν ^ 3 := by
  refine ⟨fun hA => ?_, fun ⟨ν, h⟩ => conjAut_mem_range_of_det h⟩
  obtain ⟨y, hy⟩ := hA
  obtain ⟨g, rfl⟩ := proj_surjective 3 K y
  rw [← conjAut_toGL] at hy
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq hy.symm
  refine ⟨c, ?_⟩
  rw [hc, Units.val_mul, coe_scalar_three, Matrix.det_mul, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, mul_one]
  have : ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    g.2
  rw [this, mul_one]

theorem conjAut_mem_range_of_pow_eq_one [Finite K] {A : GL (Fin 3) K} {n : ℕ}
    (h : conjAut 3 K A ^ n = 1) (hn : ¬ 3 ∣ n) :
    conjAut 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  rw [← map_pow, ← map_one (conjAut 3 K)] at h
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq h
  rw [mul_one] at hc
  have hd : (A : Matrix (Fin 3) (Fin 3) K).det ^ n = (c : K) ^ 3 := by
    have := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K).det) hc
    simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, coe_scalar_three, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one] at this
    exact this
  set δ := (A : Matrix (Fin 3) (Fin 3) K).det with hδ
  have hδ0 : δ ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  rw [conjAut_mem_range_iff]
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 3 * k + 1 ∨ n = 3 * k + 2 := ⟨n / 3, by omega⟩
  · refine ⟨c / δ ^ k, ?_⟩
    show δ = _
    rw [hk, pow_succ, pow_mul] at hd
    rw [div_pow, ← hd]
    field_simp
    ring
  · refine ⟨δ ^ (k + 1) / c, ?_⟩
    show δ = _
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    rw [hk] at hd
    rw [div_pow, ← pow_mul, show (k + 1) * 3 = 3 * k + 2 + 1 by ring, pow_succ, hd]
    field_simp

end Linear

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
