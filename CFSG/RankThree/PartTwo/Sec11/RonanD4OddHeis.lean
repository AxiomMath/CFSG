module

public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddHeisDefs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem coe_heisX (ω : F) (hω : ω ^ 3 = 1) :
    ((heisX ω hω : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![1, ω, ω ^ 2] := rfl

theorem coe_heisY :
    (((heisY : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem heisX_pow_three (ω : F) (hω : ω ^ 3 = 1) : heisX ω hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_heisX, Matrix.SpecialLinearGroup.coe_one,
    Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp [hω]
  · simp
    linear_combination (ω ^ 3 + 1) * hω

theorem heisY_pow_three : (heisY : SL(3, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_heisY, Matrix.SpecialLinearGroup.coe_one, pow_three,
    Matrix.mul_fin_three, Matrix.mul_fin_three, Matrix.one_fin_three]
  norm_num

theorem heis_commutator_mem_center (ω : F) (hω : ω ^ 3 = 1) :
    ⁅heisX ω hω, (heisY : SL(3, F))⁆ ∈ Subgroup.center SL(3, F) := by
  have hdet : (Matrix.scalar (Fin 3) ω).det = 1 := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
    linear_combination hω
  obtain ⟨c, hcc⟩ : ∃ c : SL(3, F), (c : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ω :=
    ⟨⟨Matrix.scalar (Fin 3) ω, hdet⟩, rfl⟩
  have hxy : heisX ω hω * (heisY : SL(3, F)) = c * ((heisY : SL(3, F)) * heisX ω hω) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hcc, coe_heisX, coe_heisY]
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp <;>
      first | ring1 | linear_combination -hω | linear_combination hω
  have hc : ⁅heisX ω hω, (heisY : SL(3, F))⁆ = c := by
    have h1 : ⁅heisX ω hω, (heisY : SL(3, F))⁆ =
        heisX ω hω * (heisY : SL(3, F)) * ((heisY : SL(3, F)) * heisX ω hω)⁻¹ := by
      simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    rw [h1, mul_inv_eq_iff_eq_mul]
    exact hxy
  rw [hc]
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr
    ⟨ω, by rw [Fintype.card_fin]; exact hω, hcc.symm⟩

theorem heisX_not_mem_center (ω : F) (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    heisX ω hω ∉ Subgroup.center SL(3, F) := by
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  have h0 : r = 1 := by
    have := congrFun (congrFun hr 0) 0
    simpa [coe_heisX, Matrix.scalar_apply] using this
  have h1 : r = ω := by
    have := congrFun (congrFun hr 1) 1
    simpa [coe_heisX, Matrix.scalar_apply] using this
  exact hω1 (h1.symm.trans h0)

theorem heisX_zpow_diagonal (ω : F) (hω : ω ^ 3 = 1) (i : ℤ) :
    ∃ v : Fin 3 → F,
      ((heisX ω hω ^ i : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal v := by
  refine Int.induction_on i ⟨1, ?_⟩ ?_ ?_
  · simp
  · rintro n ⟨v, hv⟩
    refine ⟨fun j => v j * ![1, ω, ω ^ 2] j, ?_⟩
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, hv, coe_heisX,
      Matrix.diagonal_mul_diagonal]
  · rintro n ⟨v, hv⟩
    refine ⟨fun j => v j * ∏ k ∈ Finset.univ.erase j, ![1, ω, ω ^ 2] k, ?_⟩
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, hv, Matrix.SpecialLinearGroup.coe_inv,
      coe_heisX, Matrix.adjugate_diagonal, Matrix.diagonal_mul_diagonal]

theorem heisY_mul_zpow_not_mem_center (ω : F) (hω : ω ^ 3 = 1) (i : ℤ) :
    (heisY : SL(3, F)) * heisX ω hω ^ i ∉ Subgroup.center SL(3, F) := by
  intro hmem
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  obtain ⟨v, hv⟩ := heisX_zpow_diagonal ω hω i
  have hent : ((heisY * heisX ω hω ^ i : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, hv]
    simp [coe_heisY, Fin.sum_univ_three, Matrix.diagonal_apply]
  have h0 := congrFun (congrFun hr 0) 0
  rw [hent] at h0
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h0
  rw [h0, Fintype.card_fin] at hr3
  norm_num at hr3

theorem heis_of_hom (ω : F) (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {Γ : Type} [Group Γ]
    (ρ : SL(3, F) →* Γ) (hker : ρ.ker ≤ Subgroup.center SL(3, F)) :
    ρ (heisX ω hω) ≠ 1 ∧ ρ (heisX ω hω) ^ 3 = 1 ∧ ρ heisY ^ 3 = 1 ∧
      Commute ⁅ρ (heisX ω hω), ρ heisY⁆ (ρ (heisX ω hω)) ∧
      Commute ⁅ρ (heisX ω hω), ρ heisY⁆ (ρ heisY) ∧
      ρ heisY ∉ Subgroup.zpowers (ρ (heisX ω hω)) := by
  have hcen := heis_commutator_mem_center ω hω
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact heisX_not_mem_center ω hω hω1 (hker (MonoidHom.mem_ker.mpr h))
  · rw [← map_pow, heisX_pow_three, map_one]
  · rw [← map_pow, heisY_pow_three, map_one]
  · rw [← map_commutatorElement]
    exact Commute.map (show Commute ⁅heisX ω hω, (heisY : SL(3, F))⁆ (heisX ω hω) from
      (Subgroup.mem_center_iff.mp hcen (heisX ω hω)).symm) ρ
  · rw [← map_commutatorElement]
    exact Commute.map (show Commute ⁅heisX ω hω, (heisY : SL(3, F))⁆ (heisY : SL(3, F)) from
      (Subgroup.mem_center_iff.mp hcen (heisY : SL(3, F))).symm) ρ
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ρ ((heisY : SL(3, F)) * heisX ω hω ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, zpow_neg, hk, mul_inv_cancel]
    exact heisY_mul_zpow_not_mem_center ω hω (-k) (hker (MonoidHom.mem_ker.mpr h1))

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
