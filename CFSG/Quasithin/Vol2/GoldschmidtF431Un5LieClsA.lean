module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocD
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem eq_of_proj_eq_Vsub {g g' : hypSU h 2 1} (hg : g ∈ Vsub h) (hg' : g' ∈ Vsub h)
    (e : hypProj h 2 1 g = hypProj h 2 1 g') : g = g' :=
  hypProj_eq_of_mem_U (Ssub_le_Usub (Vsub_le_Ssub hg)) (Ssub_le_Usub (Vsub_le_Ssub hg')) e

theorem Yof_one_Vsub : Yof (1 : hypSU h 2 1) = 0 := Yof_eq (by rw [mat_one, oddUni_zero])

theorem vE11_mem_Rt (c : h.fixedField) : vE11 c ∈ Rt h :=
  vSU_mem_Rt _ ⟨by simp [hermM], by simp [hermM], by simp [hermM]⟩

theorem eq_one_of_mem_Rt {g : hypSU h 2 1} (hg : g ∈ Rt h) (h00 : Yof g 0 0 = 0) : g = 1 := by
  obtain ⟨h01, h10, h11⟩ := hg.2
  refine (eq_one_iff_Yof_eq_zero h (Rt_le_Vsub h hg)).2 ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem R_U_Y (h : UnitaryFieldData 2 f K) : ∀ r ∈ rY h, r ∈ ucY h → r = 1 := by
  rintro _ ⟨g, hg, rfl⟩ ⟨g', hg', e⟩
  have hg'g : g' = g := eq_of_proj_eq_Vsub (Uct_le_Vsub h hg') (Rt_le_Vsub h hg) e
  rw [hg'g] at hg'
  rw [eq_one_of_mem_Rt hg hg'.2.1, map_one]

theorem R_two_Y (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    ∃ a ∈ rY h, ∃ b ∈ rY h, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have := h.charP
  obtain ⟨y, hy0, hy1⟩ := exists_ne_zero_one_F (h := h) hf
  have hne : ∀ c : h.fixedField, c ≠ 0 → hypProj h 2 1 (vE11 c) ≠ 1 := by
    intro c hc e
    rw [← map_one (hypProj h 2 1)] at e
    have h1 := congrArg Yof (eq_of_proj_eq_Vsub (Vt_le_Vsub h (vE11_mem_Vt c)) (one_mem _) e)
    rw [Yof_vE11, Yof_one_Vsub] at h1
    exact hc (Subtype.ext (by simpa using congrFun (congrFun h1 0) 0))
  refine ⟨hypProj h 2 1 (vE11 1), ⟨_, vE11_mem_Rt 1, rfl⟩, hypProj h 2 1 (vE11 y),
    ⟨_, vE11_mem_Rt y, rfl⟩, hne 1 one_ne_zero, hne y hy0, fun e => hy1 ?_⟩
  have h1 := congrArg Yof (eq_of_proj_eq_Vsub (Vt_le_Vsub h (vE11_mem_Vt 1))
    (Vt_le_Vsub h (vE11_mem_Vt y)) e)
  rw [Yof_vE11, Yof_vE11] at h1
  exact (Subtype.ext (by simpa using congrFun (congrFun h1 0) 0)).symm

end CFSG.Quasithin.H13.F431.Un.L5
