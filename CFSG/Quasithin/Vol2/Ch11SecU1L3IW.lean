module

public import CFSG.RankThree.PartOne.KF.BloomOmega

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.KFBloom
  CFSG.RankThree.PartOne.LIT
open scoped MatrixGroups

theorem eq_scalar_of_commute_adMat {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 3) (Fin 3) K} (hu : X * adMat 1 1 0 1 = adMat 1 1 0 1 * X)
    (hl : X * adMat 1 0 1 1 = adMat 1 0 1 1 * X) : X = scalar (Fin 3) (X 0 0) := by
  have eu := fun i j => congrFun (congrFun hu i) j
  have el := fun i j => congrFun (congrFun hl i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at eu el
  have u00 := eu 0 0
  have u01 := eu 0 1
  have u10 := eu 1 0
  have u11 := eu 1 1
  have u12 := eu 1 2
  have l00 := el 0 0
  have l12 := el 1 2
  have l22 := el 2 2
  simp [adMat] at u00 u01 u10 u11 u12 l00 l12 l22
  have h10 : X 1 0 = 0 := by
    have h : (2 : K) * X 1 0 = 0 := by linear_combination u00 - u10
    exact (mul_eq_zero.mp h).resolve_left h2
  have h21 : X 2 1 = 0 := by linear_combination -u11 - 2 * h10
  have h11 : X 1 1 = X 0 0 := by
    have h : (2 : K) * (X 1 1 - X 0 0) = 0 := by linear_combination u01 - h21
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2)
  have h22 : X 2 2 = X 0 0 := by linear_combination -u12 - h10 + h11
  have h01 : X 0 1 = 0 := by linear_combination -l00 - l12
  have h12 : X 1 2 = 0 := by
    have h : (2 : K) * X 1 2 = 0 := by linear_combination l22 + l12
    exact (mul_eq_zero.mp h).resolve_left h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, u10, h21, h11, h22, h01, l12, h12]

theorem eq_scalar_of_mem_centralizer_omegaGL {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    {X : GL (Fin 3) (ZMod p)} (hX : ∀ ω ∈ omegaGL M, X * ω = ω * X) :
    (X : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      scalar (Fin 3) ((X : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd two_pos h1
    omega
  obtain ⟨g, c, hc, hg⟩ := exists_congr_splitForm hp2 M hMt hdet
  have hΩ : (omegaGL M).comap (MulAut.conj g : GL (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p)) =
      omegaGL (splitForm p) := by
    rw [← omegaGL_congr, hg, omegaGL_smul _ hc]
  set Y : GL (Fin 3) (ZMod p) := g⁻¹ * X * g with hY
  have hYc : ∀ u : SL(2, ZMod p), Y * adGL u = adGL u * Y := by
    intro u
    have hu : adGL u ∈ (omegaGL M).comap
        (MulAut.conj g : GL (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p)) := by
      rw [hΩ, omegaGL_splitForm_eq_range hp]
      exact ⟨u, rfl⟩
    have h1 := hX _ (Subgroup.mem_comap.mp hu)
    change X * (g * adGL u * g⁻¹) = (g * adGL u * g⁻¹) * X at h1
    calc Y * adGL u = g⁻¹ * (X * (g * adGL u * g⁻¹)) * g := by rw [hY]; group
      _ = g⁻¹ * ((g * adGL u * g⁻¹) * X) * g := by rw [h1]
      _ = adGL u * Y := by rw [hY]; group
  have hYm : ∀ u : SL(2, ZMod p), (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      adMat (u 0 0) (u 0 1) (u 1 0) (u 1 1) =
        adMat (u 0 0) (u 0 1) (u 1 0) (u 1 1) * (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    intro u
    have h1 := congrArg Units.val (hYc u)
    rwa [Units.val_mul, Units.val_mul, coe_adGL] at h1
  have hYs := eq_scalar_of_commute_adMat (X := (Y : Matrix (Fin 3) (Fin 3) (ZMod p))) h2
    (by simpa using hYm (⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, ZMod p)))
    (by simpa using hYm (⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, ZMod p)))
  set c' := (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0
  have hXY : X = g * Y * g⁻¹ := by rw [hY]; group
  have hXm : (X : Matrix (Fin 3) (Fin 3) (ZMod p)) = scalar (Fin 3) c' := by
    calc (X : Matrix (Fin 3) (Fin 3) (ZMod p)) = (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((g⁻¹ : GL (Fin 3) (ZMod p)) :
            Matrix (Fin 3) (Fin 3) (ZMod p)) := by
          rw [hXY, Units.val_mul, Units.val_mul]
      _ = (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * scalar (Fin 3) c' *
          ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by rw [← hYs]
      _ = scalar (Fin 3) c' * ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
          rw [← (scalar_commute c' (fun r' => Commute.all c' r')
            (g : Matrix (Fin 3) (Fin 3) (ZMod p))).eq, Matrix.mul_assoc]
      _ = scalar (Fin 3) c' := by rw [Units.mul_inv, Matrix.mul_one]
  have h00 : (X : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0 = c' := by rw [hXm]; simp
  rw [h00]
  exact hXm

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
