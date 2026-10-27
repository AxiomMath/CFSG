module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin

open CFSG.SL2MinimalFaithful Matrix

namespace GE23

variable {K : Type} [Field K]

@[expose] def lowerSL (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_lowerSL (t : K) :
    ((lowerSL t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; t, 1] :=
  rfl

@[expose] def weylSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_weylSL :
    ((weylSL : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
  rfl

@[expose] def weylInvSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_weylInvSL :
    ((weylInvSL : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] :=
  rfl

theorem weylSL_inv : (weylSL : SpecialLinearGroup (Fin 2) K)⁻¹ = weylInvSL := by
  apply inv_eq_of_mul_eq_one_right
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_weylSL, coe_weylInvSL, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem weylSL_conj_unipotent (t : K) :
    (weylSL : SpecialLinearGroup (Fin 2) K) * unipotent t * weylSL⁻¹ = lowerSL (-t) := by
  rw [weylSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_unipotent, coe_weylSL, coe_weylInvSL,
      coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mulVec (t : K) (w : Fin 2 → K) :
    ((unipotent t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w =
      ![w 0 + t * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [coe_unipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mem_closure_unitriangular (γ : SpecialLinearGroup (Fin 2) K) :
    γ ∈ Subgroup.closure ({g | ∃ t : K, g = unipotent t} ∪ {g | ∃ t : K, g = lowerSL t}) := by
  set S : Set (SpecialLinearGroup (Fin 2) K) :=
    {g | ∃ t : K, g = unipotent t} ∪ {g | ∃ t : K, g = lowerSL t} with hS
  have hu : ∀ t : K, unipotent t ∈ Subgroup.closure S := fun t =>
    Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
  have hl : ∀ t : K, lowerSL t ∈ Subgroup.closure S := fun t =>
    Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rwa [Matrix.det_fin_two] at this
  have key : ∀ δ : SpecialLinearGroup (Fin 2) K, δ 1 0 ≠ 0 → δ ∈ Subgroup.closure S := by
    intro δ hδ
    have hd : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
      have := δ.2
      rwa [Matrix.det_fin_two] at this
    have e : δ = unipotent ((δ 0 0 - 1) / δ 1 0) * lowerSL (δ 1 0) *
        unipotent ((δ 1 1 - 1) / δ 1 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, coe_unipotent, coe_lowerSL, Matrix.mul_apply,
          Fin.sum_univ_two] <;> field_simp <;>
        first | ring1 | linear_combination hd | linear_combination (-1 : K) * hd
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hu _) (hl _)) (hu _)
  by_cases h : γ 1 0 = 0
  · have h1 : (lowerSL (1 : K) * γ) 1 0 ≠ 0 := by
      have ha : γ 0 0 ≠ 0 := by
        intro h0
        rw [h0, h] at hdet
        simp at hdet
      simpa [coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two, h] using ha
    have h2 := key _ h1
    have : γ = (lowerSL (1 : K))⁻¹ * (lowerSL (1 : K) * γ) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hl 1)) h2
  · exact key γ h

theorem sl2_eq_sup_conj :
    (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) =
      (unipotentHom (F := K)).range ⊔
        (unipotentHom (F := K)).range.map
          (MulAut.conj (weylSL : SpecialLinearGroup (Fin 2) K)).toMonoidHom := by
  symm
  rw [eq_top_iff]
  intro γ _
  have hγ := mem_closure_unitriangular γ
  refine (Subgroup.closure_le _).2 ?_ hγ
  rintro g (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd t, rfl⟩
  · refine Subgroup.mem_sup_right ⟨unipotent (-t), ⟨Multiplicative.ofAdd (-t), rfl⟩, ?_⟩
    simp [weylSL_conj_unipotent]

end GE23

end CFSG.Quasithin
