module

public import CFSG.Milestones.ASVolI.F437U.U5D

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem ronOdd5_short (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) {fb : E}
    (hgr : hyp.toHypF_4_4g.chart.IsGraphInv fb) :
    ∃ t : E, t ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ t ≠ 1 ∧ t * t = 1 ∧
      (¬ ∃ g ∈ Gp, g * t * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ∧
      ∃ P : Subgroup E, P ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧
        P ≤ Subgroup.centralizer ({t} : Set E) ∧ Nat.card P = 256 := by
  obtain ⟨K, fK, h, φ, hφ, hrange, h1, h2, -⟩ := burnsideF437U_U5_model hyp hgr
  haveI : Finite K := h.finite
  have hpc := burnsideF437U_U5_pCore h
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtStab h ⊓ u5LnStab h).map φ := by
    rw [show Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) by
      rw [inf_inf_distrib_left], h1, h2, Subgroup.map_inf_eq _ _ _ hφ]
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (hypUnitriangular h 2 1).map φ := by
    rw [hB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hpc]
  have hZ : ctr (oPPrime 2 (Gp ⊓ M₁)) = (ZPsub h).map φ := by
    rw [← burnsideF429a_c7_U5 hyp, hS, burnsideF437U_ctr_map φ hφ, ← centerIn_U]
    rfl
  have hZS : ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = (ZPsub h).map φ :=
    (burnsideF429a_c7_U5 hyp).trans hZ
  have hzU : z₂SU h ∈ hypUnitriangular h 2 1 :=
    (Z₂Psub_le_A₂sub.trans A₂sub_le_U) z₂SU_mem_Z₂Psub
  have hzne : z₂SU h ≠ 1 := z₂SU_ne_one
  have hzsq : z₂SU h * z₂SU h = 1 := Vsub_sq (Z₂Psub_le_Vsub z₂SU_mem_Z₂Psub)
  have hcomm : ∀ s ∈ Ssub h, s * z₂SU h = z₂SU h * s :=
    (central_Ssub_iff (Vsub_le_Ssub (Z₂Psub_le_Vsub z₂SU_mem_Z₂Psub))).2
      (Z₂Psub_le_Vsub z₂SU_mem_Z₂Psub)
  have hkey : ∀ c : hypSU h 2 1, c * z₂SU h * c⁻¹ ∉ ZPsub h := by
    intro c hw
    have hw1 : c * z₂SU h * c⁻¹ ≠ 1 := by
      intro e
      apply hzne
      calc z₂SU h = c⁻¹ * (c * z₂SU h * c⁻¹) * c := by group
        _ = 1 := by rw [e, mul_one, inv_mul_cancel]
    have hwz : c * z₂SU h * c⁻¹ = z₁SU h :=
      burnsideF437U_ZP_eq h hw z₁SU_mem_ZPsub hw1 z₁SU_ne_one
    have hproj : hypProj h 2 1 c * CFSG.Quasithin.H13.F431.Un.t5Y h *
        (hypProj h 2 1 c)⁻¹ = CFSG.Quasithin.H13.F431.Un.z5Y h := by
      have := congrArg (hypProj h 2 1) hwz
      rw [map_mul, map_mul, map_inv] at this
      exact this
    apply CFSG.Quasithin.H13.F431.Un.noconj_Y (MulAut.conj (hypProj h 2 1 c)⁻¹)
    rw [MulAut.conj_apply, inv_inv, ← hproj]
    group
  refine ⟨φ (z₂SU h), ?_, ?_, ?_, ?_, (Ssub h).map φ, ?_, ?_, ?_⟩
  · rw [hS]
    exact ⟨z₂SU h, hzU, rfl⟩
  · exact fun e => hzne (hφ (e.trans (map_one φ).symm))
  · rw [← map_mul, hzsq, map_one]
  · rintro ⟨g, hgG, hc⟩
    rw [← hrange] at hgG
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hgG
    have e : φ c * φ (z₂SU h) * (φ c)⁻¹ = φ (c * z₂SU h * c⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hZS, e] at hc
    obtain ⟨w, hw, hwe⟩ := hc
    have hw' := hφ hwe
    subst hw'
    exact hkey c hw
  · rw [hS]
    exact Subgroup.map_mono Ssub_le_Usub
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm s hs]
  · rw [Subgroup.card_map_of_injective hφ, CFSG.LocalAnalysis.EvenBN.U5.card_Ssub]
    all_goals norm_num

end CFSG.ASVolI
