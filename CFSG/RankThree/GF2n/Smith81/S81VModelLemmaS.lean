module

public import CFSG.RankThree.GF2n.Smith81.S81VModelPstab

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

private theorem trace_zero_of_pair (hσ : IsUnitaryInvolution σ) {c : F}
    (h : ∀ l : F, c * σ l + l * σ c = 0) : c = 0 := by
  by_contra hc
  have htr : ∀ z : F, z + σ z = 0 := by
    intro z
    have hl := h (σ (z * c⁻¹))
    rw [hσ.invol] at hl
    have h1 : c * (z * c⁻¹) = z := by rw [mul_comm z, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    have h2 : σ (z * c⁻¹) * σ c = σ z := by
      rw [← map_mul σ, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [h1, h2] at hl
    exact hl
  obtain ⟨c0, hc0⟩ := hσ.exists_ne
  apply hc0
  linear_combination htr c0 - CharTwo.add_self_eq_zero c0

theorem herm_eq_zero_of_form_zero (hσ : IsUnitaryInvolution σ) {H : Matrix (Fin 3) (Fin 3) F}
    (hH : cT σ H = H) (h : ∀ ρ : Fin 3 → F, ∑ i, ∑ j, ρ i * H i j * σ (ρ j) = 0) : H = 0 := by
  have hsym : ∀ i j, σ (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [cT_apply] at this
  have hq : ∀ ρ : Fin 3 → F,
      ρ 0 * H 0 0 * σ (ρ 0) + ρ 0 * H 0 1 * σ (ρ 1) + ρ 0 * H 0 2 * σ (ρ 2) +
        (ρ 1 * H 1 0 * σ (ρ 0) + ρ 1 * H 1 1 * σ (ρ 1) + ρ 1 * H 1 2 * σ (ρ 2)) +
        (ρ 2 * H 2 0 * σ (ρ 0) + ρ 2 * H 2 1 * σ (ρ 1) + ρ 2 * H 2 2 * σ (ρ 2)) = 0 := by
    intro ρ
    have := h ρ
    simp only [Fin.sum_univ_three] at this
    linear_combination this
  have hd0 : H 0 0 = 0 := by simpa using hq ![1, 0, 0]
  have hd1 : H 1 1 = 0 := by simpa using hq ![0, 1, 0]
  have hd2 : H 2 2 = 0 := by simpa using hq ![0, 0, 1]
  have hp01 : ∀ l : F, H 0 1 * σ l + l * σ (H 0 1) = 0 := by
    intro l
    have h1 := hq ![1, l, 0]
    simp [hd0, hd1] at h1
    rw [hsym 0 1]
    linear_combination h1
  have hp02 : ∀ l : F, H 0 2 * σ l + l * σ (H 0 2) = 0 := by
    intro l
    have h1 := hq ![1, 0, l]
    simp [hd0, hd2] at h1
    rw [hsym 0 2]
    linear_combination h1
  have hp12 : ∀ l : F, H 1 2 * σ l + l * σ (H 1 2) = 0 := by
    intro l
    have h1 := hq ![0, 1, l]
    simp [hd1, hd2] at h1
    rw [hsym 1 2]
    linear_combination h1
  have hc01 : H 0 1 = 0 := trace_zero_of_pair hσ hp01
  have hc02 : H 0 2 = 0 := trace_zero_of_pair hσ hp02
  have hc12 : H 1 2 = 0 := trace_zero_of_pair hσ hp12
  have hl10 : H 1 0 = 0 := by rw [← hsym 0 1, hc01, map_zero]
  have hl20 : H 2 0 = 0 := by rw [← hsym 0 2, hc02, map_zero]
  have hl21 : H 2 1 = 0 := by rw [← hsym 1 2, hc12, map_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hd0, hd1, hd2, hc01, hc02, hc12, hl10, hl20, hl21]

theorem exists_matrix_row (ρ : Fin 3 → F) (hρ : ρ ≠ 0) :
    ∃ A : Matrix (Fin 3) (Fin 3) F, A.det = 1 ∧ A 0 = ρ := by
  by_cases h0 : ρ 0 = 0
  · by_cases h1 : ρ 1 = 0
    · have h2 : ρ 2 ≠ 0 := by
        intro h2
        apply hρ
        funext k
        fin_cases k <;> simp [h0, h1, h2]
      refine ⟨!![0, 0, ρ 2; 1, 0, 0; 0, (ρ 2)⁻¹, 0], ?_, ?_⟩
      · rw [Matrix.det_fin_three]
        simp [mul_inv_cancel₀ h2]
      · funext k
        fin_cases k <;> simp [h0, h1]
    · refine ⟨!![0, ρ 1, ρ 2; 1, 0, 0; 0, 0, -(ρ 1)⁻¹], ?_, ?_⟩
      · rw [Matrix.det_fin_three]
        simp
        field_simp
      · funext k
        fin_cases k <;> simp [h0]
  · refine ⟨!![ρ 0, ρ 1, ρ 2; 0, 1, 0; 0, 0, (ρ 0)⁻¹], ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp
      field_simp
    · funext k
      fin_cases k <;> simp

variable (hσ : IsUnitaryInvolution σ) (hf : Frame σ a b) (e₀ : K ≃+* Fσ σ)

include hσ hf

theorem lemmaS_U (H : HermK σ e₀) (hH : H ≠ 0) :
    ∃ g : ↥(Pstab σ (Wa a)), tauK σ e₀ (adK hσ.invol hf e₀ g H) ≠ 0 := by
  have hHm : H.mat ≠ 0 := fun h => hH (HermK.ext (h.trans HermK.mat_zero.symm))
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin 3 → F, ∑ i, ∑ j, ρ i * H.mat i j * σ (ρ j) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hHm (herm_eq_zero_of_form_zero hσ H.cT_mat hall)
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hρ
    simp
  obtain ⟨A, hAdet, hA0⟩ := exists_matrix_row ρ hρ0
  have hA : A.det ≠ 0 := by rw [hAdet]; exact one_ne_zero
  have hdA : σ A.det = A.det := by rw [hAdet, map_one]
  obtain ⟨g, hg⟩ : ∃ g : ↥(Pstab σ (Wa a)), (g : SUid σ 6) = levi hσ.invol hf A hA hdA :=
    ⟨⟨levi hσ.invol hf A hA hdA, levi_mem_Pstab hσ.invol hf A hA hdA⟩, rfl⟩
  refine ⟨g, ?_⟩
  have hbl : blkA hσ.invol hf (g : SUid σ 6) = A := by
    rw [hg]
    exact blkA_levi hσ.invol hf A hA hdA
  have hentry : (adK hσ.invol hf e₀ g H).mat 0 0 = ∑ i, ∑ j, ρ i * H.mat i j * σ (ρ j) := by
    rw [adK_mat, hbl]
    have h := adEquiv_entry e₀ hσ.invol A hA H
    rw [adEquiv_mat] at h
    rw [h, hA0]
  intro h0
  apply hρ
  rw [← hentry]
  have ht := tauK_apply (adK hσ.invol hf e₀ g H)
  rw [h0, map_zero] at ht
  exact ht.symm.trans (by simp)

end CFSG.RankThree.GF2n.Smith81.S81V
