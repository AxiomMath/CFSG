module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieClsA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem proj_mem_centralizer_t {x : hypSU h 2 1} (hx : x * z₂SU h * x⁻¹ = z₂SU h) :
    hypProj h 2 1 x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy, t5Y, ← map_mul, ← map_mul]
  congr 1
  exact (mul_inv_eq_iff_eq_mul.1 hx).symm

theorem R_cls_Y (h : UnitaryFieldData 2 f K) : ∀ r ∈ rY h, r ≠ 1 →
    ∃ x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)), r = x * z5Y h * x⁻¹ := by
  have := h.charP
  rintro _ ⟨g, hg, rfl⟩ hne
  have hgV : g ∈ Vsub h := Rt_le_Vsub h hg
  obtain ⟨h01, h10, h11⟩ := hg.2
  have hb : h.bar (Yof g 0 0) = Yof g 0 0 := (isHerm_iff.1 (herm_Yof hgV)).1
  have hc0 : Yof g 0 0 ≠ 0 := fun hc => hne (by rw [eq_one_of_mem_Rt hg hc, map_one])
  obtain ⟨l, hl⟩ := exists_mul_bar_eq h hb
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hl, zero_mul])
  have hlb : h.bar l ≠ 0 := (map_ne_zero h.bar).2 hl0
  set A : Matrix (Fin 2) (Fin 2) K := !![l, 0; 0, (h.bar l)⁻¹] with hAdef
  have hA : IsUnit A.det := by
    rw [hAdef, Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.2 (by simpa using hl0)
  have e2 : lev (hK := h) A hA * z₂SU h * (lev (hK := h) A hA)⁻¹ = z₂SU h := by
    have hz : z₂SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_swap h)
    obtain ⟨hm, hY⟩ := lev_conj_Yof h A hA hz
    refine Yof_injOn h hm hz ?_
    rw [hY, show Yof (z₂SU h) = !![0, 1; 1, 0] from Yof_vSU (isHerm_swap h)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hAdef, Matrix.mul_apply, Fin.sum_univ_two, h.bar_bar, map_inv₀, hl0, hlb]
  have e1 : lev (hK := h) A hA * z₁SU h * (lev (hK := h) A hA)⁻¹ = g := by
    have hz : z₁SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_e₁₁ h)
    obtain ⟨hm, hY⟩ := lev_conj_Yof h A hA hz
    refine Yof_injOn h hm hgV ?_
    rw [hY, show Yof (z₁SU h) = !![1, 0; 0, 0] from Yof_vSU (isHerm_e₁₁ h)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hAdef, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h11, hl]
  refine ⟨_, proj_mem_centralizer_t e2, ?_⟩
  conv_lhs => rw [← e1]
  rw [map_mul, map_mul, map_inv]
  rfl

end CFSG.Quasithin.H13.F431.Un.L5
