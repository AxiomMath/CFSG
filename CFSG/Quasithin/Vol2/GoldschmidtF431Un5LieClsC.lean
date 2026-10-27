module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieClsB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem exists_slF_col [CharP K 2] (p r : h.fixedField) (hpr : p ≠ 0 ∨ r ≠ 0) :
    ∃ B : SpecialLinearGroup (Fin 2) h.fixedField,
      (B : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 = p ∧
        (B : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 = r := by
  by_cases hp : p = 0
  · subst hp
    have hr : r ≠ 0 := hpr.resolve_left (not_not.2 rfl)
    exact ⟨⟨!![0, r⁻¹; r, 0], by rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq, hr]⟩, rfl, rfl⟩
  · exact ⟨⟨!![p, 0; r, p⁻¹], by rw [Matrix.det_fin_two_of]; simp [hp]⟩, rfl, rfl⟩

theorem Yof_levHom_z₁SU (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    levHom h B * z₁SU h * (levHom h B)⁻¹ ∈ Vsub h ∧ ∀ i j : Fin 2,
      Yof (levHom h B * z₁SU h * (levHom h B)⁻¹) i j = slM B i 0 * slM B j 0 := by
  have hz : z₁SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_e₁₁ h)
  obtain ⟨hm, hY⟩ := Yof_levHom_conj B hz
  refine ⟨hm, fun i j => ?_⟩
  rw [hY, show Yof (z₁SU h) = !![1, 0; 0, 0] from Yof_vSU (isHerm_e₁₁ h)]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coset_Y (h : UnitaryFieldData 2 f K) (_hf : 2 ≤ f) :
    ∀ v ∈ vY h, v ∉ ucY h → ∃ x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)),
      ∃ u ∈ ucY h, v = x * z5Y h * x⁻¹ * u := by
  have := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro _ ⟨g, hg, rfl⟩ hv
  have hgV : g ∈ Vsub h := Vt_le_Vsub h hg
  have hsym : Yof g 0 1 = Yof g 1 0 := hg.2
  obtain ⟨h00, h11, h10⟩ := isHerm_iff.1 (herm_Yof hgV)
  have h01 : h.bar (Yof g 0 1) = Yof g 0 1 := h10.symm.trans hsym.symm
  obtain ⟨p, hp⟩ := exists_sqrt_F (h := h) ⟨Yof g 0 0, h.mem_fixedField.2 h00⟩
  obtain ⟨r, hr⟩ := exists_sqrt_F (h := h) ⟨Yof g 1 1, h.mem_fixedField.2 h11⟩
  have hp' : (p : K) * p = Yof g 0 0 := congrArg Subtype.val hp
  have hr' : (r : K) * r = Yof g 1 1 := congrArg Subtype.val hr
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    refine hv ⟨g, ⟨hgV, ?_, ?_, hsym⟩, rfl⟩
    · rw [← hp', hcon.1]
      simp
    · rw [← hr', hcon.2]
      simp
  obtain ⟨B, hB0, hB1⟩ := exists_slF_col p r hpr
  obtain ⟨hg₀, hY₀⟩ := Yof_levHom_z₁SU B
  have hs0 : slM B 0 0 = (p : K) := by rw [slM_apply, hB0]
  have hs1 : slM B 1 0 = (r : K) := by rw [slM_apply, hB1]
  set g₀ := levHom h B * z₁SU h * (levHom h B)⁻¹ with hg₀def
  set e : h.fixedField := p * r + ⟨Yof g 0 1, h.mem_fixedField.2 h01⟩ with he
  have hJ : g₀ * g = vJ e := by
    refine Yof_injOn h (mul_mem hg₀ hgV) (Vt_le_Vsub h (vJ_mem_Vt e)) ?_
    rw [Yof_mul_Vsub hg₀ hgV, Yof_vJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hY₀, hs0, hs1, he]
    · linear_combination hp' + (Yof g 0 0) * h2
    · linear_combination (-1 : K) * hsym
    · linear_combination hr' + (Yof g 1 1) * h2
  have hgeq : g = g₀ * vJ e := by
    calc g = g₀⁻¹ * (g₀ * g) := (inv_mul_cancel_left g₀ g).symm
      _ = g₀ * vJ e := by rw [hJ, inv_eq_self_of_mem_Vsub hg₀]
  refine ⟨hypProj h 2 1 (levHom h B), proj_mem_centralizer_t (levHom_conj_z₂SU B),
    hypProj h 2 1 (vJ e), ⟨vJ e, vJ_mem_Uct e, rfl⟩, ?_⟩
  rw [hgeq, hg₀def, map_mul, map_mul, map_mul, map_inv]
  rfl

end CFSG.Quasithin.H13.F431.Un.L5
