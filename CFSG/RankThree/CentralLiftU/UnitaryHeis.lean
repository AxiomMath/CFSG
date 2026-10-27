module

public import CFSG.RankThree.CentralLiftU.HypRankOneOdd

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2W coe_sl2W)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def heisUMat (u v : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, u, v; 0, 1, -h.bar u; 0, 0, 1]

@[expose] noncomputable def heisLMat (z t : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; z, 1, 0; t, -h.bar z, 1]

variable {h}

theorem heisUMat_mem {u v : K} (huv : v + h.bar v = -(u * h.bar u)) :
    ((heisUMat h u v).map h.bar)ᵀ * gramJ3 K * heisUMat h u v = gramJ3 K ∧
      (heisUMat h u v).det = 1 := by
  refine ⟨?_, by simp [heisUMat, det_fin_three]⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [heisUMat, gramJ3, Matrix.mul_apply, Fin.sum_univ_three, h.bar_bar]
  linear_combination huv

theorem heisLMat_mem {z t : K} (hzt : t + h.bar t = -(z * h.bar z)) :
    ((heisLMat h z t).map h.bar)ᵀ * gramJ3 K * heisLMat h z t = gramJ3 K ∧
      (heisLMat h z t).det = 1 := by
  refine ⟨?_, by simp [heisLMat, det_fin_three]⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [heisLMat, gramJ3, Matrix.mul_apply, Fin.sum_univ_three, h.bar_bar]
  linear_combination hzt

variable (h)

@[expose] noncomputable def heisU {u v : K} (huv : v + h.bar v = -(u * h.bar u)) :
    gramSU h (gramJ3 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (heisUMat h u v)
      (by rw [(heisUMat_mem huv).2]; exact one_ne_zero),
    by rw [mem_gramSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; exact heisUMat_mem huv⟩

@[expose] noncomputable def heisL {z t : K} (hzt : t + h.bar t = -(z * h.bar z)) :
    gramSU h (gramJ3 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (heisLMat h z t)
      (by rw [(heisLMat_mem hzt).2]; exact one_ne_zero),
    by rw [mem_gramSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; exact heisLMat_mem hzt⟩

theorem coe_heisU {u v : K} (huv : v + h.bar v = -(u * h.bar u)) :
    ((heisU h huv : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisUMat h u v :=
  rfl

theorem coe_heisL {z t : K} (hzt : t + h.bar t = -(z * h.bar z)) :
    ((heisL h hzt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisLMat h z t :=
  rfl

@[expose] def heisUpper : Set (gramSU h (gramJ3 K)) :=
  {X | ∃ u v : K, v + h.bar v = -(u * h.bar u) ∧
    ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisUMat h u v}

@[expose] def heisLower : Set (gramSU h (gramJ3 K)) :=
  {X | ∃ z t : K, t + h.bar t = -(z * h.bar z) ∧
    ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisLMat h z t}

theorem heisU_mem {u v : K} (huv : v + h.bar v = -(u * h.bar u)) : heisU h huv ∈ heisUpper h :=
  ⟨u, v, huv, rfl⟩

theorem heisL_mem {z t : K} (hzt : t + h.bar t = -(z * h.bar z)) : heisL h hzt ∈ heisLower h :=
  ⟨z, t, hzt, rfl⟩

variable {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

omit hc0 in
include hc in
theorem bar_c : h.bar c = -c := by
  have : c + h.bar c = 0 := hc
  linear_combination this

include hc in
theorem coe_iota3_sl2W :
    ((iota3 h hc hc0 sl2W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, -c⁻¹; 0, 1, 0; c, 0, 0] := by
  rw [coe_iota3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [iota3Mat, sl2W]

theorem heisU_v_ne_zero {X : gramSU h (gramJ3 K)} (hX : X ∈ heisUpper h) (hX1 : X ≠ 1) :
    ∃ u v : K, ∃ huv : v + h.bar v = -(u * h.bar u), X = heisU h huv ∧ v ≠ 0 := by
  obtain ⟨u, v, huv, hXm⟩ := hX
  refine ⟨u, v, huv, Subtype.ext (Units.ext hXm), fun hv => hX1 ?_⟩
  subst hv
  have hu : u * h.bar u = 0 := by
    rw [map_zero, add_zero] at huv
    linear_combination huv
  have hu0 : u = 0 := by
    rcases mul_eq_zero.1 hu with hu | hu
    · exact hu
    · exact (h.bar_eq_zero_iff).1 hu
  subst hu0
  apply Subtype.ext
  apply Units.ext
  rw [hXm]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [heisUMat, one_apply]

include hc hc0 in
theorem heisU_mul_iota3_sl2W {u v : K} (huv : v + h.bar v = -(u * h.bar u)) (hv : v ≠ 0) :
    ∃ (hzt : (1 / v) + h.bar (1 / v) = -((-h.bar u / v) * h.bar (-h.bar u / v)))
      (huv' : (-1 / (c ^ 2 * v)) + h.bar (-1 / (c ^ 2 * v)) =
        -((u / (c * v)) * h.bar (u / (c * v)))),
      heisU h huv * iota3 h hc hc0 sl2W =
        heisL h hzt * dkHom h (Units.mk0 (c * v) (mul_ne_zero hc0 hv)) * heisU h huv' := by
  have hbc : h.bar c = -c := bar_c h hc
  have hbv : h.bar v ≠ 0 := (h.bar_eq_zero_iff).not.mpr hv
  have hvv : h.bar v = -v - u * h.bar u := by linear_combination huv
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_div₀, map_neg, map_one, h.bar_bar]
    field_simp
    linear_combination huv
  · simp only [map_div₀, map_neg, map_one, map_mul, map_pow, hbc]
    field_simp
    linear_combination -huv
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [coe_heisU, coe_iota3_sl2W h hc hc0, coe_heisL, coe_dkHom, coe_heisU]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [heisUMat, heisLMat, dkVec, Matrix.mul_apply, Fin.sum_univ_three, hbc, h.bar_bar,
        map_div₀, map_neg, vecMul_diagonal] <;>
      field_simp
    all_goals first | ring1 | linear_combination huv
end CFSG.RankThree.CentralLiftU
