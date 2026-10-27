module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement

private theorem k328r1f_omega_facts {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : (2 : F) = 0 ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  refine ⟨h2, by linear_combination (ω - 1) * hω, ?_, ?_⟩
  · rintro rfl
    exact one_ne_zero (by linear_combination hω - h2)
  · intro h
    exact one_ne_zero (by linear_combination hω - h - ω * h2)

private theorem k328r1f_orderOf_diag {F : Type} [Field F] (g : GL (Fin 4) F) (v : Fin 4 → F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal v) (h3 : ∀ i, v i ^ 3 = 1)
    (i : Fin 4) (hi : v i ≠ 1) : orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow, Units.val_one]
    have : v ^ 3 = 1 := funext fun j => by simpa using h3 j
    rw [this, Matrix.diagonal_one']
  · intro h1
    apply hi
    have := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F) i i) h1
    simpa [hg] using this

private theorem k328r1f_not_mem_zpowers {F : Type} [Field F] {ω : F} (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1])
    (ho : orderOf z₀ = 3) (h1 : ω ≠ 1) (h2 : ω ^ 2 ≠ ω) : t₀ ∉ Subgroup.zpowers z₀ := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hmod := zpow_mod_orderOf z₀ k
  rw [ho] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [hk] at hmod
  have e00 : (t₀ : Matrix (Fin 4) (Fin 4) F) 0 0 = ω := by rw [ht]; simp
  have e11 : (t₀ : Matrix (Fin 4) (Fin 4) F) 1 1 = ω ^ 2 := by rw [ht]; simp
  have f11 : (z₀ : Matrix (Fin 4) (Fin 4) F) 1 1 = ω := by rw [hz]; simp
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h0 | h0
  · rw [h0, zpow_zero] at hmod
    apply h1
    have := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F) 0 0) hmod
    simpa [e00] using this.symm
  · rw [h0, zpow_one] at hmod
    apply h2
    have := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F) 1 1) hmod
    rw [e11, f11] at this
    exact this.symm
  · rw [h0, zpow_two] at hmod
    apply h2
    have := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F) 0 0) hmod
    simp only [Units.val_mul, hz, e00, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq] at this
    simp at this
    rw [sq]
    exact this

private theorem k328r1f_exists_gl {F : Type} [Field F] (M : Matrix (Fin 4) (Fin 4) F)
    (h : M.det = 1) : ∃ g : GL (Fin 4) F, (g : Matrix (Fin 4) (Fin 4) F) = M :=
  ⟨((Matrix.isUnit_iff_isUnit_det M).2 (by rw [h]; exact isUnit_one)).unit, IsUnit.unit_spec _⟩

private theorem k328r1f_mem_centralizer {F : Type} [Field F] {z₀ g : GL (Fin 4) F}
    (hdet : (g : Matrix (Fin 4) (Fin 4) F).det = 1)
    (hcomm : (z₀ : Matrix (Fin 4) (Fin 4) F) * g = g * z₀) :
    g ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀} := by
  refine ⟨CFSG.Open.StatedAPI.mem_statedSL_of_det hdet, ?_⟩
  show g ∈ Subgroup.centralizer {z₀}
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Units.ext (by simpa using hcomm.symm)

private theorem k328r1f_commutator_eq {F : Type} [Field F] {g d z : GL (Fin 4) F}
    (h : (g : Matrix (Fin 4) (Fin 4) F) * d = z * d * g) : ⁅g, d⁆ = z := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact Units.ext (by simpa using h)

private theorem k328r1f_z_mem {F : Type} [Field F] {ω : F} (hω3 : ω ^ 3 = 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ ∈ stdComp (StatedSL 4 F) z₀ := by
  obtain ⟨P, hP⟩ := k328r1f_exists_gl (F := F)
    !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1] (by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove])
  obtain ⟨D, hD⟩ := k328r1f_exists_gl (F := F) (Matrix.diagonal ![1, ω ^ 2, ω, 1]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp
    linear_combination hω3)
  have hPc : (z₀ : Matrix (Fin 4) (Fin 4) F) * P = P * z₀ := by
    rw [hP, hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have hDc : (z₀ : Matrix (Fin 4) (Fin 4) F) * D = D * z₀ := by
    rw [hD, hz, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hkey : (P : Matrix (Fin 4) (Fin 4) F) * D = z₀ * D * P := by
    rw [hP, hD, hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    all_goals first | ring1 | linear_combination hω3 | linear_combination (-1 : F) * hω3
  have hdetP : (P : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hP, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  have hdetD : (D : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_four]
    simp
    linear_combination hω3
  have hmem := Subgroup.commutator_mem_commutator (k328r1f_mem_centralizer hdetP hPc)
    (k328r1f_mem_centralizer hdetD hDc)
  rwa [k328r1f_commutator_eq hkey] at hmem

private theorem k328r1f_t_mem {F : Type} [Field F] {ω : F} (h2 : (2 : F) = 0) (hω3 : ω ^ 3 = 1)
    (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    t₀ ∈ stdComp (StatedSL 4 F) z₀ := by
  obtain ⟨τ, hτ⟩ := k328r1f_exists_gl (F := F)
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
      linear_combination (-1 : F) * h2)
  obtain ⟨D, hD⟩ := k328r1f_exists_gl (F := F) (Matrix.diagonal ![1, ω, ω ^ 2, 1]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp
    linear_combination hω3)
  have hτc : (z₀ : Matrix (Fin 4) (Fin 4) F) * τ = τ * z₀ := by
    rw [hτ, hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have hDc : (z₀ : Matrix (Fin 4) (Fin 4) F) * D = D * z₀ := by
    rw [hD, hz, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hkey : (τ : Matrix (Fin 4) (Fin 4) F) * D = t₀ * D * τ := by
    rw [hτ, hD, ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    all_goals first | ring1 | linear_combination hω3 | linear_combination (-1 : F) * hω3
  have hdetτ : (τ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hτ, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
    linear_combination (-1 : F) * h2
  have hdetD : (D : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_four]
    simp
    linear_combination hω3
  have hmem := Subgroup.commutator_mem_commutator (k328r1f_mem_centralizer hdetτ hτc)
    (k328r1f_mem_centralizer hdetD hDc)
  rwa [k328r1f_commutator_eq hkey] at hmem

theorem row1_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    FactsLeaf (StatedSL 4 F) z₀ t₀ := by
  obtain ⟨h2, hω3, hω1, hω2⟩ := k328r1f_omega_facts hF hω
  have hzC := k328r1f_z_mem hω3 z₀ hz
  have ho₁ : orderOf z₀ = 3 :=
    k328r1f_orderOf_diag z₀ ![ω, ω, ω, 1] hz
      (fun i => by fin_cases i <;> simp [hω3]) 0 (by simpa using hω1)
  have ho₂ : orderOf t₀ = 3 :=
    k328r1f_orderOf_diag t₀ ![ω, ω ^ 2, 1, 1] ht
      (fun i => by
        fin_cases i <;> simp
        · exact hω3
        · linear_combination (ω ^ 3 + 1) * hω3)
      0 (by simpa using hω1)
  refine ⟨stdComp_le _ _ hzC, hzC, k328r1f_t_mem h2 hω3 z₀ t₀ hz ht, ho₁, ho₂, ?_,
    k328r1f_not_mem_zpowers z₀ t₀ hz ht ho₁ hω1 hω2⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, ht, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
