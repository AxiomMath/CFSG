module

public import CFSG.Milestones.ASVolI.F429.aC7Gen
public import CFSG.Milestones.ASVolI.F429.aU5Chart

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section U5Model

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem burnsideF429a_U5_U_le_borel : hypProjUnitriangular h 2 1 ≤ hypProjBorel h 2 1 := by
  rw [← normalizer_hypProjUnitriangular h (by norm_num) (by norm_num)]
  exact Subgroup.le_normalizer

theorem burnsideF429a_U5_pCoreOf_borel :
    pCoreOf 2 (u5PtP h ⊓ u5LnP h) = hypProjUnitriangular h 2 1 := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [u5PtP_inf_u5LnP]
  refine burnsideF429a_pCoreOf_eq_of_sylow
    (burnsideF429_isSylowOf_of_le (u5_sylow h) burnsideF429a_U5_U_le_borel le_top) ?_
  intro b hb u hu
  rw [← normalizer_hypProjUnitriangular h (by norm_num) (by norm_num)] at hb
  exact (Subgroup.mem_normalizer_iff.mp hb u).mp hu

theorem burnsideF429a_U5_ctr_U :
    ctr (hypProjUnitriangular h 2 1) = (ZPsub h).map (hypProj h 2 1) := by
  apply le_antisymm
  · rintro z ⟨-, hz⟩
    exact centralizer_le_map_ZPsub hz
  · rintro _ ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨z, ZPsub_le_U hz, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, ZPsub_commute hz hu]

theorem burnsideF429a_U5_ctr_oPPrime :
    ctr (oPPrime 2 (u5PtP h)) = (ZPsub h).map (hypProj h 2 1) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hUP : hypProjUnitriangular h 2 1 ≤ u5PtP h := burnsideF429a_U5_U_le_borel.trans
    (hypProjBorel_le_projIsoStabilizer h le_rfl (by norm_num))
  have hSyl : ChF.IsSylowOf 2 (hypProjUnitriangular h 2 1) (u5PtP h) :=
    burnsideF429_isSylowOf_of_le (u5_sylow h) hUP le_top
  apply le_antisymm
  · rintro z ⟨-, hz⟩
    apply centralizer_le_map_ZPsub
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huO : u ∈ oPPrime 2 (u5PtP h) := by
      obtain ⟨k, hk⟩ := hSyl.2.1 ⟨u, hu⟩
      exact burnsideF4gU4Inv_mem_oPPrime (hUP hu) (k := k)
        (by simpa using congrArg Subtype.val hk)
    exact Subgroup.mem_centralizer_iff.1 hz u huO
  · exact burnsideF429a_le_ctr_oPPrime hSyl burnsideF429a_U5_ctr_U.ge fun p hp l hl =>
      (Subgroup.mem_normalizer_iff.mp (u5PtP_le_normalizer hp) l).mp hl

end U5Model

theorem burnsideF429a_c7_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨Ψ, e1, e2⟩ := burnsideF429a_U5_equiv marking
  obtain ⟨k1, k2, -⟩ := burnsideF429a_model_ctr Ψ (h1.trans e1) (h2.trans e2)
  rw [k1, k2, burnsideF429a_U5_pCoreOf_borel, burnsideF429a_U5_ctr_U,
    burnsideF429a_U5_ctr_oPPrime]

end CFSG.ASVolI
