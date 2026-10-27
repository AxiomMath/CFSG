module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylE

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem syl_uni_decomp (h : UnitaryFieldData 2 2 K) {x : hypPSU h 2 1}
    (hxU : x ∈ hypProjUnitriangular h 2 1)
    (hx : x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) :
    ∃ a : h.fixedField, ∃ s ∈ Ssub h,
      x = hypProj h 2 1 (levHom h (CFSG.LieType.Universal.Spin.upperSL2 a) * s) := by
  obtain ⟨u, hu, rfl⟩ := hxU
  obtain ⟨A, C, x', d, -, hC, hd, hA, hAJ, hmat⟩ :=
    syl_decomp_of_comm ((syl_mem_centralizer_iff u).1 hx)
  obtain ⟨⟨d00, d11, -, -, -⟩, ⟨l10, -, -, -, -, -, -, -, -, -⟩⟩ := U_entries hu
  have hA00 : A 0 0 = 1 := by rw [hA]; exact d00
  have hA11 : A 1 1 = 1 := by rw [hA]; exact d11
  have hA10 : A 1 0 = 0 := by rw [hA]; exact l10
  have hbar : h.bar (A 0 1) = A 0 1 := by
    obtain ⟨e00, -, -, -⟩ := syl_entries hAJ
    have := h.charP
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [hA00, map_one] at e00
    linear_combination e00 - A 0 1 * h2
  let a : h.fixedField := ⟨A 0 1, hbar⟩
  have hAeq : A = slM (CFSG.LieType.Universal.Spin.upperSL2 a) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slM_apply, a, hA00, hA11, hA10]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two, hA00, hA11, hA10]
    ring
  have hd1 : d = 1 := by rw [hd, hdet, map_one, div_one]
  obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub (hK := h) hC
  refine ⟨a, s, hs, ?_⟩
  congr 1
  apply mat_injective
  rw [mat_mul, syl_mat_levHom, hsm, hmat, hd1, hAeq]

end CFSG.Quasithin.H13.F431.Un.L5
