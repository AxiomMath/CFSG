module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieWC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.QuasithinUnique CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5w_xz_zero {u : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (hfix : ∀ a b, hK.bar (mat u a b) = mat u a b) :
    mat u ιe₁ ιz = 0 ∧ mat u ιe₂ ιz = 0 := by
  have := hK.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  obtain ⟨-, -, -, -, r5, r6⟩ := U_rel hu
  simp only [hfix] at r5 r6
  refine ⟨?_, ?_⟩
  · refine mul_self_eq_zero.1 ?_
    linear_combination (-1 : K) * r6 + h2 (mat u ιe₁ ιf₁) -
      (mat u ιe₁ ιe₂ * mat u ιe₁ ιf₂) * CharTwo.two_eq_zero (R := K)
  · refine mul_self_eq_zero.1 ?_
    linear_combination (-1 : K) * r5 + h2 (mat u ιe₂ ιf₂)

theorem un5w_mem_Vsub {u : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (hfix : ∀ a b, hK.bar (mat u a b) = mat u a b)
    (hc : ∀ v ∈ hypUnitriangular hK 2 1, fieldAut hK (bar5 hK) v = v → v * u = u * v) :
    u ∈ Vsub hK := by
  obtain ⟨v, hvV, hYv, hvfix⟩ := un5w_exists_v hK
  have e := (commute_Vsub_entries hu hvV
    (hc v (Ssub_le_Usub (Vsub_le_Ssub hvV)) (hvfix _)).symm).1
  rw [hYv] at e
  have ha : aOf u = 0 := by simpa using e
  obtain ⟨hx1, hx2⟩ := un5w_xz_zero hK hu hfix
  refine (mem_Vsub_iff ((mem_Ssub_iff hu).2 ha)).2 fun i => ?_
  fin_cases i
  · exact hx1
  · exact hx2

theorem un5w_Yof_11 {u : hypSU hK 2 1} (huV : u ∈ Vsub hK)
    (hc : ∀ v ∈ hypUnitriangular hK 2 1, fieldAut hK (bar5 hK) v = v → v * u = u * v) :
    Yof u 1 1 = 0 := by
  obtain ⟨g, hgU, hga, hgfix⟩ := un5w_exists_g hK
  have e := (commute_Vsub_entries hgU huV (hc g hgU (hgfix _))).1
  rwa [hga, one_mul] at e

theorem un5w_Yof_10 {u : hypSU hK 2 1} (huV : u ∈ Vsub hK)
    (hfix : ∀ a b, hK.bar (mat u a b) = mat u a b) : Yof u 1 0 = Yof u 0 1 := by
  rw [(isHerm_iff.1 (herm_Yof huV)).2.2]
  exact hfix (.inl 0) (.inr (.inr 1))

theorem un5w_mem_ZPsub {u : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (huV : u ∈ Vsub hK) (h01 : Yof u 0 1 = 0) (h11 : Yof u 1 1 = 0) : u ∈ ZPsub hK := by
  have ha : mat u ιe₁ ιe₂ = 0 := (mem_Ssub_iff hu).1 (Vsub_le_Ssub huV)
  have hx := (mem_Vsub_iff (Vsub_le_Ssub huV)).1 huV
  have hx1 : mat u ιe₁ ιz = 0 := hx 0
  have hx2 : mat u ιe₂ ιz = 0 := hx 1
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hu
  have h12 : mat u ιe₁ ιf₂ = 0 := h01
  have h22 : mat u ιe₂ ιf₂ = 0 := h11
  rw [mem_ZPsub]
  refine ⟨hu, ha, ?_, hx1, ?_, hx2, ?_, h12, ?_, h22⟩
  · rw [r1, ha, map_zero]
  · simp [r3, hx1, hx2, ha]
  · rw [r2, hx2, map_zero]
  · simp [r4, h12, ha, h22, hx1, hx2]

end CFSG.Quasithin.H13.F431.Un.OL5
