module

public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.RankThree.PartOne.S15K

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.KCLinComm

variable {K : Type} [Field K]

theorem exists_pow_four_eq [Finite K] [CharP K 2] (c : K) : ∃ μ : K, μ ^ 4 = c := by
  have h2 : Function.Surjective (fun x : K => x ^ 2) := by
    refine Finite.surjective_of_injective ?_
    intro a b hab
    exact frobenius_inj K 2 (by simpa [frobenius_def] using hab)
  obtain ⟨y, hy⟩ := h2 c
  obtain ⟨μ, hμ⟩ := h2 y
  refine ⟨μ, ?_⟩
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  simpa [hμ] using hy

theorem eq_one_of_pow_four_eq_one [CharP K 2] {x : K} (hx : x ^ 4 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h : (x - 1) ^ 4 = 0 := by
    linear_combination hx + (-2 * x ^ 3 + 3 * x ^ 2 - 2 * x + 1) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

theorem exists_sl_lift_of_pow_eq_one [Finite K] [CharP K 2] {p : ℕ} (A : GL (Fin 4) K)
    (hA : (conjAut 4 K A) ^ p = 1) :
    ∃ B : GL (Fin 4) K, conjAut 4 K B = conjAut 4 K A ∧
      (B : Matrix (Fin 4) (Fin 4) K).det = 1 ∧ B ^ p = 1 := by
  have hn : 3 ≤ 4 := by norm_num
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn (A ^ p)).1 (by rw [map_pow]; exact hA)
  set d : Kˣ := Matrix.GeneralLinearGroup.det A with hd
  obtain ⟨μ0, hμ0⟩ := exists_pow_four_eq (K := K) ((d⁻¹ : Kˣ) : K)
  have hμ0ne : μ0 ≠ 0 := by
    rintro rfl
    have h0 : ((d⁻¹ : Kˣ) : K) = 0 := by rw [← hμ0]; norm_num
    exact (d⁻¹).ne_zero h0
  set μ : Kˣ := Units.mk0 μ0 hμ0ne with hμ
  have hμ4 : (μ : K) ^ 4 = ((d⁻¹ : Kˣ) : K) := hμ0
  set B : GL (Fin 4) K := GeneralLinearGroup.scalar (Fin 4) μ * A with hB
  have hdetB : (B : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    have hdet : (B : Matrix (Fin 4) (Fin 4) K).det =
        (μ : K) ^ 4 * (A : Matrix (Fin 4) (Fin 4) K).det := by
      rw [hB, Units.val_mul, Matrix.det_mul, det_scalar_gl]
    rw [hdet, hμ4]
    have : (A : Matrix (Fin 4) (Fin 4) K).det = (d : K) := rfl
    rw [this, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBp : B ^ p = GeneralLinearGroup.scalar (Fin 4) (μ ^ p * c) := by
    rw [hB, (commute_scalar_gl (K := K) (n := 4) μ A).mul_pow, ← hc, map_mul, map_pow]
  have hν : μ ^ p * c = 1 := by
    have hdetU : Matrix.GeneralLinearGroup.det B = 1 := Units.ext hdetB
    have h1 : ((B ^ p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_pow, hdetU, one_pow, Units.val_one]
    rw [hBp, det_scalar_gl] at h1
    exact Units.ext (eq_one_of_pow_four_eq_one h1)
  refine ⟨B, ?_, hdetB, ?_⟩
  · rw [hB, map_mul, (conjAut_eq_one_iff hn _).2 ⟨μ, rfl⟩, one_mul]
  · rw [hBp, hν, map_one]

theorem mul_comm_of_conjAut_commute [Finite K] [CharP K 2] {B B' : GL (Fin 4) K}
    (hB : (B : Matrix (Fin 4) (Fin 4) K).det = 1) (hB' : (B' : Matrix (Fin 4) (Fin 4) K).det = 1)
    (h : conjAut 4 K B * conjAut 4 K B' = conjAut 4 K B' * conjAut 4 K B) : B * B' = B' * B := by
  have hn : 3 ≤ 4 := by norm_num
  have hC : conjAut 4 K (B * B' * B⁻¹ * B'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨ζ, hζ⟩ := (conjAut_eq_one_iff hn _).1 hC
  have hdet : ((B * B' * B⁻¹ * B'⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    have hBu : Matrix.GeneralLinearGroup.det B = 1 := Units.ext hB
    have hB'u : Matrix.GeneralLinearGroup.det B' = 1 := Units.ext hB'
    have : Matrix.GeneralLinearGroup.det (B * B' * B⁻¹ * B'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hBu, hB'u]
      simp
    rw [← Matrix.GeneralLinearGroup.val_det_apply, this, Units.val_one]
  rw [← hζ, det_scalar_gl] at hdet
  have hζ1 : ζ = 1 := Units.ext (eq_one_of_pow_four_eq_one hdet)
  rw [hζ1, map_one] at hζ
  have : B * B' * B⁻¹ * B'⁻¹ = 1 := hζ.symm
  calc B * B' = (B * B' * B⁻¹ * B'⁻¹) * (B' * B) := by group
    _ = B' * B := by rw [this, one_mul]

end CFSG.RankThree.PartOne.S15K
