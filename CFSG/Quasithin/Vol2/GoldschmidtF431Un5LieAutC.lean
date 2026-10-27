module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieAutB
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Aut

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {x : Gam h}

theorem trace_Ypp (hc : lmat x * nN K = nN K * lmat x) (S : Matrix (Fin 2) (Fin 2) K) :
    (Jm K * (Aee x * S * (Jm K * (Aee x)⁻¹ * Jm K))).trace = (S * Jm K).trace := by
  have h1 := Aee_inv_mul hc
  calc (Jm K * (Aee x * S * (Jm K * (Aee x)⁻¹ * Jm K))).trace
      = ((Aee x * S * (Jm K * (Aee x)⁻¹ * Jm K)) * Jm K).trace := Matrix.trace_mul_comm _ _
    _ = (Aee x * (S * Jm K * (Aee x)⁻¹)).trace := by
        simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = ((S * Jm K * (Aee x)⁻¹) * Aee x).trace := Matrix.trace_mul_comm _ _
    _ = (S * Jm K).trace := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem Ypp_smul_Jm (hc : lmat x * nN K = nN K * lmat x) (c : K) :
    Aee x * (c • Jm K) * (Jm K * (Aee x)⁻¹ * Jm K) = c • Jm K := by
  have h2 := Aee_mul_inv hc
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc Aee x * Jm K * (Jm K * (Aee x)⁻¹ * Jm K) = Aee x * ((Aee x)⁻¹ * Jm K) := by
        simp only [Matrix.mul_assoc, Jm_mul_mul_self]
    _ = Jm K := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem aut_core_vt (hφ : Phi h x (t5Y h) = t5Y h) : ∀ g ∈ Vt h, act h x g ∈ Vt h := by
  have := h.charP
  have hc := lmat_comm_nN x (act_z₂SU_eq x hφ)
  intro g hg
  obtain ⟨Y', hY', hsym, rfl⟩ := mem_vsub_iff.1 hg
  obtain ⟨Y'', hm, hY''⟩ := exists_Ypp hc hY'
  have hH : IsHerm h Y'' := herm_of_mem_Vsub hm
  have hS : Y'' 1 0 + Y'' 0 1 = 0 := by
    have ht := trace_Ypp hc (Y'.map x.1.right)
    rw [← hY'', trace_Jm_mul, trace_mul_Jm] at ht
    rw [ht]
    simp only [Matrix.map_apply, hsym]
    exact CharTwo.add_self_eq_zero _
  exact mem_vsub_iff.2 ⟨Y'', hH, (CharTwo.add_eq_zero.1 hS).symm,
    mat_injective (hm.trans (mat_vSU hH).symm)⟩

theorem aut_core_uc (hφ : Phi h x (t5Y h) = t5Y h) : ∀ g ∈ Uct h, act h x g ∈ Uct h := by
  have hc := lmat_comm_nN x (act_z₂SU_eq x hφ)
  intro g hg
  obtain ⟨Y', hY', ⟨h00, h11, h01⟩, rfl⟩ := mem_vsub_iff.1 hg
  obtain ⟨Y'', hm, hY''⟩ := exists_Ypp hc hY'
  have hH : IsHerm h Y'' := herm_of_mem_Vsub hm
  have hYJ : Y' = Y' 0 1 • Jm K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, h00, h11, h01]
  have hS : Y'.map x.1.right = x.1.right (Y' 0 1) • Jm K := by
    rw [hYJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm]
  have hY2 : Y'' = x.1.right (Y' 0 1) • Jm K := by
    rw [hY'', hS, Ypp_smul_Jm hc]
  refine mem_vsub_iff.2 ⟨Y'', hH, ?_, mat_injective (hm.trans (mat_vSU hH).symm)⟩
  rw [hY2]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Jm]

end Aut

section Final

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem aut_vY (φ : MulAut (hypPSU h 2 1)) (hφ : φ (t5Y h) = t5Y h) :
    ∀ v ∈ vY h, φ v ∈ vY h := by
  obtain ⟨x, rfl⟩ := Phi_surjective h φ
  rintro _ ⟨g, hg, rfl⟩
  rw [Phi_apply]
  exact ⟨act h x g, aut_core_vt hφ g hg, rfl⟩

theorem aut_ucY (φ : MulAut (hypPSU h 2 1)) (hφ : φ (t5Y h) = t5Y h) :
    ∀ u ∈ ucY h, φ u ∈ ucY h := by
  obtain ⟨x, rfl⟩ := Phi_surjective h φ
  rintro _ ⟨g, hg, rfl⟩
  rw [Phi_apply]
  exact ⟨act h x g, aut_core_uc hφ g hg, rfl⟩

end Final

end CFSG.Quasithin.H13.F431.Un.L5
