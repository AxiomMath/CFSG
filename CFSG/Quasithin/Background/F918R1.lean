module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

@[expose] def modActR {d : ℕ} {F : Type} [Field F] (b : Bool) (γ : GL (Fin d) F) (x : Fin d → F) :
    Fin d → F :=
  if b then (γ : Matrix (Fin d) (Fin d) F) *ᵥ x else ((γ⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ *ᵥ x

section Action

variable {d : ℕ} {F : Type} [Field F]

theorem modActR_true (γ : GL (Fin d) F) (x : Fin d → F) :
    modActR true γ x = (γ : Matrix (Fin d) (Fin d) F) *ᵥ x := rfl

theorem modActR_false (γ : GL (Fin d) F) (x : Fin d → F) :
    modActR false γ x = ((γ⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ *ᵥ x := rfl

theorem modActR_one (b : Bool) (x : Fin d → F) : modActR b 1 x = x := by
  cases b <;> simp [modActR]

theorem modActR_mul (b : Bool) (g h : GL (Fin d) F) (x : Fin d → F) :
    modActR b (g * h) x = modActR b g (modActR b h x) := by
  cases b <;> simp [modActR, _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.mulVec_mulVec]

private theorem mem_statedSL_of_det {γ : GL (Fin d) F}
    (h : (γ : Matrix (Fin d) (Fin d) F).det = 1) : γ ∈ StatedSL d F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

private theorem transvection_mulVec_eq (i j : Fin d) (c : F) (y : Fin d → F) :
    transvection i j c *ᵥ y = y + Pi.single i (c * y j) := by
  ext r
  simp [transvection, Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply,
    Function.update_apply]

private theorem transpose_transvection (i j : Fin d) (c : F) :
    (transvection i j c)ᵀ = transvection j i c := by
  simp [transvection, transpose_single]

private def tvGL {i j : Fin d} (hij : i ≠ j) (c : F) : GL (Fin d) F where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by rw [transvection_mul_transvection_same _ _ hij, add_neg_cancel, transvection_zero]
  inv_val := by rw [transvection_mul_transvection_same _ _ hij, neg_add_cancel, transvection_zero]

private theorem tvGL_mem {i j : Fin d} (hij : i ≠ j) (c : F) : tvGL hij c ∈ StatedSL d F :=
  mem_statedSL_of_det (det_transvection_of_ne _ _ hij c)

private theorem modActR_true_tvGL {i j : Fin d} (hij : i ≠ j) (c : F) (y : Fin d → F) :
    modActR true (tvGL hij c) y = y + Pi.single i (c * y j) :=
  transvection_mulVec_eq i j c y

private theorem modActR_false_tvGL {i j : Fin d} (hij : i ≠ j) (c : F) (y : Fin d → F) :
    modActR false (tvGL hij c) y = y + Pi.single j (-c * y i) := by
  rw [modActR_false]
  change (transvection i j (-c))ᵀ *ᵥ y = _
  rw [transpose_transvection, transvection_mulVec_eq]

private theorem eq_zero_of_add_single_eq {i : Fin d} {a : F} {y : Fin d → F}
    (h : y + Pi.single i a = y) : a = 0 := by
  simpa using congrFun h i

end Action

section Transitive

variable {d : ℕ} {F : Type} [Field F]

private theorem exists_det_eq_one_mulVec_single {i l : Fin d} (hli : l ≠ i) {v : Fin d → F}
    (hv : v ≠ 0) : ∃ M : Matrix (Fin d) (Fin d) F, M.det = 1 ∧ M *ᵥ Pi.single i 1 = v := by
  have case1 : ∀ u : Fin d → F, u i ≠ 0 →
      ∃ M : Matrix (Fin d) (Fin d) F, M.det = 1 ∧ M *ᵥ Pi.single i 1 = u := by
    intro u hu
    have hdet : (updateCol (1 : Matrix (Fin d) (Fin d) F) i u).det = u i := by
      rw [← cramer_apply, cramer_one]
      rfl
    refine ⟨updateCol 1 i u * diagonal (Function.update 1 l (u i)⁻¹), ?_, ?_⟩
    · rw [det_mul, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ l), hdet]
      simp [hu]
    · rw [← mulVec_mulVec, diagonal_mulVec_single, Function.update_of_ne hli.symm]
      ext r
      simp
  by_cases hvi : v i = 0
  · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := Function.ne_iff.mp hv
    have hik : i ≠ k := by
      rintro rfl
      exact hk hvi
    obtain ⟨M, hdet, hM⟩ :=
      case1 (transvection i k 1 *ᵥ v) (by simp [transvection_mulVec_eq, hvi, hk])
    refine ⟨transvection i k (-1) * M, ?_, ?_⟩
    · rw [det_mul, det_transvection_of_ne _ _ hik, hdet, one_mul]
    · rw [← mulVec_mulVec, hM, mulVec_mulVec, transvection_mul_transvection_same _ _ hik,
        neg_add_cancel, transvection_zero, one_mulVec]
  · exact case1 v hvi

private theorem exists_det_eq_one_mulVec_eq (hd : 2 ≤ d) {v w : Fin d → F} (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ M : Matrix (Fin d) (Fin d) F, M.det = 1 ∧ M *ᵥ v = w := by
  have hli : (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := by simp
  obtain ⟨A, hA, hAv⟩ := exists_det_eq_one_mulVec_single hli hv
  obtain ⟨B, hB, hBw⟩ := exists_det_eq_one_mulVec_single hli hw
  have hAu : IsUnit A.det := by
    rw [hA]
    exact isUnit_one
  refine ⟨B * A⁻¹, ?_, ?_⟩
  · rw [det_mul, det_nonsing_inv, hA, hB, Ring.inverse_one, mul_one]
  · rw [← hAv, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul A hAu, Matrix.mul_one, hBw]

private noncomputable def unitOfDetOne {M : Matrix (Fin d) (Fin d) F} (h : M.det = 1) :
    GL (Fin d) F where
  val := M
  inv := M⁻¹
  val_inv := mul_nonsing_inv M (by rw [h]; exact isUnit_one)
  inv_val := nonsing_inv_mul M (by rw [h]; exact isUnit_one)

end Transitive

theorem exists_modActR_eq {d : ℕ} {F : Type} [Field F] (hd : 2 ≤ d) (b : Bool)
    {v w : Fin d → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ γ ∈ StatedSL d F, modActR b γ v = w := by
  obtain ⟨M, hM, hMv⟩ := exists_det_eq_one_mulVec_eq hd hv hw
  cases b
  · have hMt : Mᵀ.det = 1 := by rw [det_transpose, hM]
    refine ⟨(unitOfDetOne hMt)⁻¹, Subgroup.inv_mem _ (mem_statedSL_of_det hMt), ?_⟩
    rw [modActR_false, inv_inv]
    change Mᵀᵀ *ᵥ v = w
    rw [transpose_transpose, hMv]
  · exact ⟨unitOfDetOne hM, mem_statedSL_of_det hM, hMv⟩

section Fixed

variable {d : ℕ} {F : Type} [Field F]

private theorem exists_ne_ne (hd : 3 ≤ d) (a b : Fin d) : ∃ c : Fin d, c ≠ a ∧ c ≠ b := by
  by_contra! h
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
  omega

private theorem coord_eq_zero_of_stab_fix (hd : 3 ≤ d) (b₁ b₂ : Bool) {i₀ k : Fin d}
    (hk : k ≠ i₀) {y : Fin d → F}
    (hy : ∀ γ ∈ StatedSL d F, modActR b₁ γ (Pi.single i₀ 1) = Pi.single i₀ 1 →
      modActR b₂ γ y = y) : y k = 0 := by
  obtain ⟨j, hj0, hjk⟩ := exists_ne_ne hd i₀ k
  cases b₁ <;> cases b₂
  · have h := hy (tvGL hk 1) (tvGL_mem hk 1) (by simp [modActR_false_tvGL, hk])
    rw [modActR_false_tvGL] at h
    simpa using eq_zero_of_add_single_eq h
  · have h := hy (tvGL hjk 1) (tvGL_mem hjk 1) (by simp [modActR_false_tvGL, hj0])
    rw [modActR_true_tvGL] at h
    simpa using eq_zero_of_add_single_eq h
  · have h := hy (tvGL hjk.symm 1) (tvGL_mem hjk.symm 1) (by simp [modActR_true_tvGL, hj0])
    rw [modActR_false_tvGL] at h
    simpa using eq_zero_of_add_single_eq h
  · have h := hy (tvGL hk.symm 1) (tvGL_mem hk.symm 1) (by simp [modActR_true_tvGL, hk])
    rw [modActR_true_tvGL] at h
    simpa using eq_zero_of_add_single_eq h

end Fixed

theorem fix_card_le_modActR {d : ℕ} {F : Type} [Field F] [Finite F] (hd : 3 ≤ d) (b₁ b₂ : Bool)
    {v : Fin d → F} (hv : v ≠ 0) :
    Nat.card {x : Fin d → F // ∀ γ ∈ StatedSL d F, modActR b₁ γ v = v → modActR b₂ γ x = x} ≤
      Nat.card F := by
  obtain ⟨i₀⟩ : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have he : (Pi.single i₀ (1 : F) : Fin d → F) ≠ 0 := by
    intro h
    simpa using congrFun h i₀
  obtain ⟨g, hgS, hg⟩ := exists_modActR_eq (by omega) b₁ he hv
  have key : ∀ x : Fin d → F, (∀ γ ∈ StatedSL d F, modActR b₁ γ v = v → modActR b₂ γ x = x) →
      ∀ k, k ≠ i₀ → modActR b₂ g⁻¹ x k = 0 := by
    intro x hx k hk
    refine coord_eq_zero_of_stab_fix hd b₁ b₂ hk fun γ hγS hγ => ?_
    have hfix : modActR b₁ (g * γ * g⁻¹) v = v := by
      rw [← hg, modActR_mul, modActR_mul, ← modActR_mul b₁ g⁻¹ g, inv_mul_cancel, modActR_one,
        hγ]
    have h1 := hx _ (mul_mem (mul_mem hgS hγS) (inv_mem hgS)) hfix
    calc modActR b₂ γ (modActR b₂ g⁻¹ x)
        = modActR b₂ g⁻¹ (modActR b₂ (g * γ * g⁻¹) x) := by
          rw [← modActR_mul, ← modActR_mul]
          congr 1
          group
      _ = modActR b₂ g⁻¹ x := by rw [h1]
  refine Nat.card_le_card_of_injective (fun x => modActR b₂ g⁻¹ x.1 i₀) fun x y hxy => ?_
  have hcoord : modActR b₂ g⁻¹ x.1 = modActR b₂ g⁻¹ y.1 := by
    funext k
    by_cases hk : k = i₀
    · subst hk
      exact hxy
    · rw [key x.1 x.2 k hk, key y.1 y.2 k hk]
  have h := congrArg (modActR b₂ g) hcoord
  rw [← modActR_mul, ← modActR_mul, mul_inv_cancel, modActR_one, modActR_one] at h
  exact Subtype.ext h

end CFSG.Quasithin
