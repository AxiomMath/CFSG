module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.RankThree.GF2n.Smith81

open Matrix CFSG.Open

private theorem eq_zero_of_fixed_dual_stab_std {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (hK : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1) {w : Fin n → K}
    (hw : ∀ g : GL (Fin n) K, (g : Matrix (Fin n) (Fin n) K).det = 1 →
      (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single ⟨0, by omega⟩ 1 ∈
        Submodule.span K {Pi.single ⟨0, by omega⟩ 1} →
      (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single ⟨1, by omega⟩ 1 = Pi.single ⟨1, by omega⟩ 1 →
      (g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ w = w) : w = 0 := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hi : ∀ i, i ≠ i2 → w i = 0 := by
    intro i hi
    let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (transvection i i2 1)
      (by rw [det_transvection_of_ne _ _ hi]; exact one_ne_zero)
    have hcol : ∀ j, j ≠ i2 → (transvection i i2 (1 : K)) *ᵥ Pi.single j 1 = Pi.single j 1 := by
      intro j hj
      ext k
      simp [transvection, Matrix.add_mulVec, Matrix.mulVec_single, Matrix.single_apply, Ne.symm hj,
        Matrix.one_apply, Pi.single_apply, eq_comm]
    have h := hw g (det_transvection_of_ne i i2 hi (1 : K))
      (by
        show transvection i i2 (1 : K) *ᵥ _ ∈ _
        rw [hcol i0 h02]; exact Submodule.mem_span_singleton_self _)
      (hcol i1 h12)
    have h2 := congrFun h i2
    simp [g, transvection, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, add_mul, ite_mul, Finset.sum_add_distrib] at h2
    simpa using h2
  obtain ⟨μ, hμ0, hμ1⟩ := hK
  have h2 : w i2 = 0 := by
    let dv : Fin n → K := Function.update (Function.update 1 i0 μ) i2 μ⁻¹
    have hdet : (diagonal dv).det = 1 := by
      rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _),
        Finset.prod_update_of_mem (by simp [h02] : i0 ∈ Finset.univ \ {i2})]
      simp [hμ0]
    let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal dv)
      (by rw [hdet]; exact one_ne_zero)
    have h := hw g hdet
      (by
        show diagonal dv *ᵥ _ ∈ _
        refine Submodule.mem_span_singleton.mpr ⟨μ, ?_⟩
        funext k
        by_cases hk : k = i0
        · subst hk; simp [Matrix.mulVec_diagonal, dv, h02]
        · simp [Matrix.mulVec_diagonal, dv, Pi.single_apply, hk])
      (by
        show diagonal dv *ᵥ _ = _
        funext k
        by_cases hk : k = i1
        · subst hk
          have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
          simp [Matrix.mulVec_diagonal, dv, h12, h10]
        · simp [Matrix.mulVec_diagonal, dv, Pi.single_apply, hk])
    have h2 := congrFun h i2
    simp [g, dv, Matrix.mulVec_diagonal] at h2
    by_contra hw2
    apply hμ1
    have h3 : μ⁻¹ * w i2 = 1 * w i2 := by rw [one_mul]; exact h2
    exact inv_eq_one.mp (mul_right_cancel₀ hw2 h3)
  funext i
  by_cases h : i = i2
  · rw [h, h2]; rfl
  · exact hi i h

private theorem exists_isUnit_cols_pair {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {c x : Fin n → K} (hcx : LinearIndependent K ![c, x]) :
    ∃ F : Matrix (Fin n) (Fin n) K, IsUnit F ∧ F *ᵥ Pi.single ⟨0, by omega⟩ 1 = c ∧
      F *ᵥ Pi.single ⟨1, by omega⟩ 1 = x := by
  have key : ∀ k, (hk : 2 ≤ k) → k ≤ n → ∃ b : Fin k → (Fin n → K), LinearIndependent K b ∧
      b ⟨0, by omega⟩ = c ∧ b ⟨1, by omega⟩ = x := by
    intro k hk hkn
    induction k, hk using Nat.le_induction with
    | base => exact ⟨![c, x], hcx, rfl, rfl⟩
    | succ k hk ih =>
      obtain ⟨b, hb, hb0, hb1⟩ := ih (by omega)
      obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_finrank hb
        (by rw [Module.finrank_fin_fun]; omega)
      refine ⟨Fin.snoc b y, hy, ?_, ?_⟩
      · have : (⟨0, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨0, by omega⟩ := rfl
        rw [this, Fin.snoc_castSucc, hb0]
      · have : (⟨1, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨1, by omega⟩ := rfl
        rw [this, Fin.snoc_castSucc, hb1]
  obtain ⟨b, hb, hb0, hb1⟩ := key n hn le_rfl
  refine ⟨Matrix.of fun i j => b j i, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_cols_iff_isUnit.mp hb
  · rw [Matrix.mulVec_single_one]; exact hb0
  · rw [Matrix.mulVec_single_one]; exact hb1

theorem eq_zero_of_fixed_dual_stab {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (hK : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1) {c x w : Fin n → K} (hcx : LinearIndependent K ![c, x])
    (hw : ∀ g : GL (Fin n) K, g ∈ StatedSL n K →
      (g : Matrix (Fin n) (Fin n) K) *ᵥ c ∈ Submodule.span K {c} →
      (g : Matrix (Fin n) (Fin n) K) *ᵥ x = x →
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ w = w) : w = 0 := by
  obtain ⟨F, hF, hF0, hF1⟩ := exists_isUnit_cols_pair (by omega) hcx
  set Fu : GL (Fin n) K := hF.unit
  have hFu : (Fu : Matrix (Fin n) (Fin n) K) = F := rfl
  have hstd := eq_zero_of_fixed_dual_stab_std hn hK (w := Fᵀ *ᵥ w) (by
    intro g hdet hg0 hg1
    set h : GL (Fin n) K := Fu * g * Fu⁻¹
    have hhF : (h : Matrix (Fin n) (Fin n) K) * F = F * g := by
      simp only [h, Units.val_mul, hFu, Matrix.mul_assoc]
      rw [← hFu, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have hmv : ∀ v, (h : Matrix (Fin n) (Fin n) K) *ᵥ (F *ᵥ v) =
        F *ᵥ ((g : Matrix _ _ K) *ᵥ v) := by
      intro v; rw [Matrix.mulVec_mulVec, hhF, ← Matrix.mulVec_mulVec]
    have hdet' : (h : Matrix (Fin n) (Fin n) K).det = 1 := by
      simp only [h, Units.val_mul, Matrix.det_mul, hdet, mul_one]
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have h1 := hw h (StatedAPI.mem_statedSL_of_det hdet')
      (by
        rw [← hF0, hmv]
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hg0
        rw [← ha, Matrix.mulVec_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩)
      (by rw [← hF1, hmv, hg1])
    have hh : h⁻¹ * Fu = Fu * g⁻¹ := by simp only [h]; group
    have hinv : Fᵀ * ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * Fᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← hFu, ← Units.val_mul,
        ← Units.val_mul, hh]
    have h2 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ (Fᵀ *ᵥ w) = Fᵀ *ᵥ w := by
      rw [Matrix.mulVec_mulVec, ← hinv, ← Matrix.mulVec_mulVec, h1]
    calc (g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ (Fᵀ *ᵥ w)
        = (g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ (Fᵀ *ᵥ w)) := by rw [h2]
      _ = Fᵀ *ᵥ w := by
          rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, Matrix.transpose_one, Matrix.one_mulVec])
  have hFt : IsUnit Fᵀ := (Matrix.isUnit_transpose F).mpr hF
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hFt
  exact hinj (by rw [hstd, Matrix.mulVec_zero])

end CFSG.RankThree.GF2n.Smith81
