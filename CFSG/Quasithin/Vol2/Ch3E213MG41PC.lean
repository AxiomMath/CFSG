module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD1
public import CFSG.Quasithin.Vol2.Ch3E213MG41S1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2]

structure CaseB (G₀ : Subgroup (antiSp k)) (F₁ : Subfield k) (e e' : Fin 4 → k) : Prop where
  four : 4 ≤ Nat.card F₁
  supp : e 1 = 0 ∧ e 2 = 0 ∧ e' 1 = 0 ∧ e' 2 = 0
  bil : spBil e e' = 1
  image : ∀ z ∈ Refl.normC G₀, z 2 = 0 → proj z ≠ 0 →
    ∃ a ∈ F₁, ∃ b ∈ F₁, proj z = a • e + b • e'
  cover : ∀ a ∈ F₁, ∀ b ∈ F₁, (a ≠ 0 ∨ b ≠ 0) →
    ∃ z ∈ Refl.normC G₀, z 2 = 0 ∧ proj z = a • e + b • e'
  trans : ∀ z ∈ Refl.normC G₀, z 2 = 0 → proj z ≠ 0 → ∀ a ∈ F₁, ∀ b ∈ F₁, (a ≠ 0 ∨ b ≠ 0) →
    ∃ g ∈ G₀, natAct g (eOne k) = eOne k ∧ proj (natAct g z) = a • e + b • e'

omit [CharP k 2] in
theorem eq_proj_add {z : Fin 4 → k} (hz : z 2 = 0) : z = proj z + z 1 • eOne k := by
  funext i
  fin_cases i <;> simp [proj, eOne, hz]

omit [CharP k 2] in
theorem proj_eq_self {x : Fin 4 → k} (h1 : x 1 = 0) (h2 : x 2 = 0) : proj x = x := by
  funext i
  fin_cases i <;> simp [proj, h1, h2]

omit [CharP k 2] in
theorem proj_add (u v : Fin 4 → k) : proj (u + v) = proj u + proj v := by
  funext i
  fin_cases i <;> simp [proj]

omit [CharP k 2] in
theorem proj_smul (c : k) (u : Fin 4 → k) : proj (c • u) = c • proj u := by
  funext i
  fin_cases i <;> simp [proj]

omit [CharP k 2] in
theorem proj_eOne : proj (eOne k) = 0 := by
  funext i
  fin_cases i <;> simp [proj, eOne]

omit [CharP k 2] in
theorem bil_eTwo_left (x : Fin 4 → k) : spBil (Pi.single 2 1) x = x 1 := by
  rw [bil_symm, bil_single]
  rfl

variable {G₀ : Subgroup (antiSp k)} {F₁ : Subfield k} {e e' : Fin 4 → k}

theorem CaseB.bil_frame (hB : CaseB G₀ F₁ e e') (a b l a' b' l' : k) :
    spBil (a • e + b • e' + l • eOne k) (a' • e + b' • e' + l' • eOne k) = a * b' + b * a' := by
  obtain ⟨-, he2, -, he2'⟩ := hB.supp
  have h1 : spBil e' e = 1 := by rw [bil_symm]; exact hB.bil
  have hρe : spBil (eOne k) e = 0 := by rw [bil_eOne_left]; exact he2
  have hρe' : spBil (eOne k) e' = 0 := by rw [bil_eOne_left]; exact he2'
  have heρ : spBil e (eOne k) = 0 := by rw [bil_eOne]; exact he2
  have he'ρ : spBil e' (eOne k) = 0 := by rw [bil_eOne]; exact he2'
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self,
    hB.bil, h1, hρe, hρe', heρ, he'ρ]
  ring

theorem CaseB.bil_left_frame (hB : CaseB G₀ F₁ e e') (a b l : k) :
    spBil e' (a • e + b • e' + l • eOne k) = a := by
  simpa only [zero_smul, one_smul, zero_add, add_zero, zero_mul, one_mul] using
    hB.bil_frame 0 1 0 a b l

theorem CaseB.bil_right_frame (hB : CaseB G₀ F₁ e e') (a b l : k) :
    spBil e (a • e + b • e' + l • eOne k) = b := by
  simpa only [zero_smul, one_smul, zero_add, add_zero, zero_mul, one_mul] using
    hB.bil_frame 1 0 0 a b l

theorem CaseB.frame_apply (hB : CaseB G₀ F₁ e e') (a b l : k) :
    (a • e + b • e' + l • eOne k) 1 = l ∧ (a • e + b • e' + l • eOne k) 2 = 0 ∧
      proj (a • e + b • e' + l • eOne k) = a • e + b • e' := by
  obtain ⟨he1, he2, he1', he2'⟩ := hB.supp
  refine ⟨by simp [eOne, he1, he1'], by simp [eOne, he2, he2'], ?_⟩
  rw [proj_add, proj_add, proj_smul, proj_smul, proj_smul, proj_eOne, proj_eq_self he1 he2,
    proj_eq_self he1' he2', smul_zero, add_zero]

theorem CaseB.frame_ne_zero (hB : CaseB G₀ F₁ e e') {a b : k} (hab : a ≠ 0 ∨ b ≠ 0) :
    a • e + b • e' ≠ 0 := by
  intro h
  have h1 := hB.bil_left_frame a b 0
  have h2 := hB.bil_right_frame a b 0
  rw [zero_smul, add_zero, h, map_zero] at h1 h2
  rcases hab with hab | hab
  · exact hab h1.symm
  · exact hab h2.symm

theorem CaseB.bil_eq (hB : CaseB G₀ F₁ e e') (x y : Fin 4 → k) :
    spBil x y = spBil e' x * spBil e y + spBil e' y * spBil e x + x 1 * y 2 + y 1 * x 2 := by
  obtain ⟨he1, he2, he1', he2'⟩ := hB.supp
  have hb := hB.bil
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [bil_apply, he1, he2, he1', he2', zero_mul, mul_zero, add_zero] at hb ⊢
  linear_combination (-(x 0 * y 3 + x 3 * y 0)) * hb +
    (-(e' 0 * e 0 * x 3 * y 3 + e' 3 * e 3 * x 0 * y 0)) * h2

end CFSG.Quasithin.Ch3E213M.G41.Big
