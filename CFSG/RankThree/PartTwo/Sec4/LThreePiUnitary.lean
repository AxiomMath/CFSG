module

public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem conjTr_conjTr_of_invol (hσ : ∀ c, σ (σ c) = c) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσ]

theorem det_conjTr {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : (conjTr σ M).det = σ M.det := by
  rw [conjTr, det_transpose]
  exact (RingHom.map_det (σ : K →+* K) M).symm

theorem conjTr_diagonal {n : ℕ} (d : Fin n → K) :
    conjTr σ (diagonal d) = diagonal fun i => σ (d i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [conjTr]
  · simp [conjTr, diagonal_apply_ne _ hij, diagonal_apply_ne _ (Ne.symm hij)]

theorem exists_unitary_conj (hσ : IsUnitaryInvolution σ) {d : Fin 3 → K}
    (hd : ∀ i, σ (d i) * d i = 1)
    (hdd : (d 0 ≠ d 1 ∧ d 0 ≠ d 2 ∧ d 1 ≠ d 2) ∨ (d 0 ≠ d 1 ∧ d 1 = d 2))
    {y g : Matrix (Fin 3) (Fin 3) K} (hy : conjTr σ y * y = 1) (hg : IsUnit g)
    (hyg : y * g = g * diagonal d) :
    ∃ g' : Matrix (Fin 3) (Fin 3) K, conjTr σ g' * g' = 1 ∧ y * g' = g' * diagonal d := by
  set G := conjTr σ g * g with hGdef
  have hGh : conjTr σ G = G := by
    rw [hGdef, conjTr_mul, conjTr_conjTr_of_invol hσ.invol]
  have hgdet : g.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det g).mp hg |>.ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hGdef, det_mul, det_conjTr]
    exact mul_ne_zero ((map_ne_zero σ).mpr hgdet) hgdet
  have hGD : conjTr σ (diagonal d) * G * diagonal d = G := by
    have h1 : conjTr σ (y * g) * (y * g) = G := by
      rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ y), hy, Matrix.one_mul]
    rw [hyg, conjTr_mul, Matrix.mul_assoc] at h1
    calc conjTr σ (diagonal d) * G * diagonal d
        = conjTr σ (diagonal d) * (conjTr σ g * (g * diagonal d)) := by
          rw [hGdef]; simp only [Matrix.mul_assoc]
      _ = G := h1
  have hentry : ∀ i j, G i j = σ (d i) * G i j * d j := by
    intro i j
    have := congrFun (congrFun hGD i) j
    rw [conjTr_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this.symm
  have hd0 : ∀ i, d i ≠ 0 := fun i h0 => by
    have := hd i
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hoff : ∀ i j, d i ≠ d j → G i j = 0 := by
    intro i j hij
    have hσd : σ (d i) = (d i)⁻¹ := eq_inv_of_mul_eq_one_left (hd i)
    have e := hentry i j
    rw [hσd] at e
    have : G i j * (d i - d j) = 0 := by
      have e' : G i j * d i = G i j * d j := by
        calc G i j * d i = (d i)⁻¹ * G i j * d j * d i := by rw [← e]
          _ = G i j * d j := by field_simp [hd0 i]
      rw [mul_sub, e', sub_self]
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hij)
  have hGfix : ∀ i j, σ (G j i) = G i j := fun i j => by
    have := congrFun (congrFun hGh i) j
    simpa [conjTr] using this
  rcases hdd with ⟨h01, h02, h12⟩ | ⟨h01, h12⟩
  ·
    have g01 := hoff 0 1 h01
    have g02 := hoff 0 2 h02
    have g12 := hoff 1 2 h12
    have g10 := hoff 1 0 (Ne.symm h01)
    have g20 := hoff 2 0 (Ne.symm h02)
    have g21 := hoff 2 1 (Ne.symm h12)
    have hGdiag : G = diagonal fun i => G i i := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [g01, g02, g12, g10, g20, g21]
    have hγ : ∀ i, G i i ≠ 0 := by
      intro i h
      apply hGdet
      rw [hGdiag, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h
    choose c hc using fun i => hσ.norm_surj (G i i)⁻¹ (by rw [map_inv₀, hGfix]) (inv_ne_zero (hγ i))
    refine ⟨g * diagonal c, ?_, ?_⟩
    · rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ g), ← hGdef, hGdiag,
        conjTr_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      calc σ (c i) * (G i i * c i) = G i i * (σ (c i) * c i) := by ring
        _ = 1 := by rw [hc i, mul_inv_cancel₀ (hγ i)]
    · rw [← Matrix.mul_assoc, hyg, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_diagonal,
        diagonal_mul_diagonal]
      congr 2
      funext i
      ring
  ·
    have h02 : d 0 ≠ d 2 := h12 ▸ h01
    have g01 := hoff 0 1 h01
    have g02 := hoff 0 2 h02
    have g10 := hoff 1 0 (Ne.symm h01)
    have g20 := hoff 2 0 (Ne.symm h02)
    set G' : Matrix (Fin 2) (Fin 2) K := !![G 1 1, G 1 2; G 2 1, G 2 2] with hG'def
    have hG'h : conjTr σ G' = G' := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjTr, hG'def, hGfix]
    have hdetG : G.det = G 0 0 * G'.det := by
      rw [det_fin_three, det_fin_two, hG'def]
      simp [g01, g02, g10, g20]
      ring
    have hγ : G 0 0 ≠ 0 := fun h => hGdet (by rw [hdetG, h, zero_mul])
    have hG'det : G'.det ≠ 0 := fun h => hGdet (by rw [hdetG, h, mul_zero])
    obtain ⟨P', hP'⟩ :=
      CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hσ hG'h hG'det
    obtain ⟨c, hc⟩ := hσ.norm_surj (G 0 0)⁻¹ (by rw [map_inv₀, hGfix]) (inv_ne_zero hγ)
    set Q : Matrix (Fin 2) (Fin 2) K := (P' : Matrix (Fin 2) (Fin 2) K) with hQ
    set P : Matrix (Fin 3) (Fin 3) K := !![c, 0, 0; 0, Q 0 0, Q 0 1; 0, Q 1 0, Q 1 1] with hP
    have e00 := congrFun (congrFun hP' 0) 0
    have e01 := congrFun (congrFun hP' 0) 1
    have e10 := congrFun (congrFun hP' 1) 0
    have e11 := congrFun (congrFun hP' 1) 1
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hG'def] at e00 e01 e10 e11
    refine ⟨g * P, ?_, ?_⟩
    · rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ g), ← hGdef]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three, hP, g01, g02, g10, g20]
      · calc σ c * (G 0 0 * c) = G 0 0 * (σ c * c) := by ring
          _ = 1 := by rw [hc, mul_inv_cancel₀ hγ]
      · linear_combination e00
      · linear_combination e01
      · linear_combination e10
      · linear_combination e11
    · have hPD : P * diagonal d = diagonal d * P := by
        ext i j
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
        fin_cases i <;> fin_cases j <;> simp [hP, h12, mul_comm]
      rw [← Matrix.mul_assoc, hyg, Matrix.mul_assoc, Matrix.mul_assoc, hPD]

end CFSG.RankThree.PartTwo.Sec4
