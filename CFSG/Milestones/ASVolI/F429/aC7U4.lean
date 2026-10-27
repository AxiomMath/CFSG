module

public import CFSG.Milestones.ASVolI.F429.aC7Gen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section U4Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429a_U4_comm_zRad {g z : hypSU h 2 0} (hg : g ∈ parP h) (hchi : chi h g = 1)
    (hz : z ∈ zRad h) : g * z = z * g := by
  obtain ⟨c, -, hzc⟩ := hz
  have hcol := (mem_parP_iff h g).mp hg
  obtain ⟨hrow, hdiag⟩ := row_if1_of_col h g hcol
  have h11 : ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 := hchi
  have hf11 : ((g : GL Ix K) : Matrix Ix Ix K) if1 if1 = 1 := by
    rw [h11, map_one, one_mul] at hdiag
    exact hdiag
  have c2 := hcol ie2 ie2_ne_ie1
  have c3 := hcol if1 if1_ne_ie1
  have c4 := hcol if2 if2_ne_ie1
  have r2 := hrow ie2 ie2_ne_if1
  have r4 := hrow if2 if2_ne_if1
  apply hypSU_ext
  rw [coe_mul_hypSU, coe_mul_hypSU, hzc]
  ext i j
  rw [mul_apply, mul_apply, sum_ix, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, h11, hf11, c2, c3, c4, r2, r4] <;> ring

theorem burnsideF429a_U4_ctr_oPPrime : ctr (oPPrime 2 (parP h)) = zRad h := by
  refine le_antisymm (burnsideF4gU4Inv_ctr_oPPrime_le h) fun z hz => Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact burnsideF4gU4Inv_mem_oPPrime (radQ_le_parP h (zRad_le_radQ h hz)) (k := 1)
      (by rw [pow_one, pow_two]; exact burnsideF4gU4Inv_zRad_sq h hz)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxK := burnsideF4gU4Inv_oPPrime_le_chiKer h hx
    exact burnsideF429a_U4_comm_zRad h hxK.1 hxK.2 hz

end U4Model

theorem burnsideF429a_c7_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, e1, e2⟩ := burnsideF4gU4_exists_equiv marking
  obtain ⟨k1, k2, -⟩ := burnsideF429a_model_ctr Φ (h1.trans e1) (h2.trans e2)
  rw [k1, k2, burnsideF4gU4Inv_pCore_borel, burnsideF4gU4Inv_ctr_U, burnsideF429a_U4_ctr_oPPrime]

end CFSG.ASVolI
