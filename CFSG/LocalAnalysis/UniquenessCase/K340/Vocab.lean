module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
public import CFSG.Quasithin.Background.C118Partner
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_eq_quasithin (X : Subgroup G) :
    thompsonJ X = CFSG.Quasithin.thompsonJ X := by
  rw [thompsonJ, CFSG.inSubgroup]
  exact CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ X

theorem omegaOneZJ_eq_quasithin (X : Subgroup G) :
    omegaOneZJ X = CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ X) := by
  rw [omegaOneZJ, CFSG.inSubgroup]
  exact CFSG.Quasithin.elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf X

section Sylow

variable {H T : Subgroup G} (P : Sylow 2 ↥H)
  (hP : (P : Subgroup ↥H).map H.subtype = T)

include hP

theorem map_thompsonJ_sylow :
    (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)).map H.subtype = thompsonJ T := by
  rw [thompsonJ_eq_quasithin T, ← hP]
  exact (CFSG.Quasithin.thompsonJ_map_of_injective' H.subtype_injective
    (P : Subgroup ↥H)).symm

theorem map_Hone :
    (CFSG.QuasithinUnique.Setup.Campbell.Hone P).map H.subtype = thompsonJ H := by
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf T H := by
    have hsub : (P.map H.subtype).subgroupOf H = (P : Subgroup ↥H) := by
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hP]; exact Subgroup.map_subtype_le _
    · rw [← hP]; exact P.isPGroup'.map H.subtype
    · rw [← hP, hsub]; exact P.not_dvd_index
  have hJ : CFSG.Quasithin.thompsonJ T ≤ CFSG.Quasithin.thompsonJ H :=
    CFSG.Quasithin.B6.thompsonJ_le_of_sylow hT
  have hN : ((CFSG.Quasithin.thompsonJ H).comap H.subtype).Normal := by
    have h : ((CFSG.Quasithin.thompsonJ H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.Quasithin.B6.thompsonJ_le H)).mpr (CFSG.Quasithin.B6.le_normalizer_thompsonJ H)
    rw [← Subgroup.comap_subtype] at h
    exact h
  haveI := hN
  have hone_le :
      (CFSG.QuasithinUnique.Setup.Campbell.Hone P).map H.subtype ≤ thompsonJ H := by
    rw [CFSG.QuasithinUnique.Setup.Campbell.Hone, Subgroup.map_le_iff_le_comap,
      thompsonJ_eq_quasithin H]
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    change H.subtype x ∈ CFSG.Quasithin.thompsonJ H
    refine hJ ?_
    rw [← thompsonJ_eq_quasithin T, ← map_thompsonJ_sylow P hP]
    exact Subgroup.mem_map_of_mem H.subtype hx
  have hJL : CFSG.Quasithin.thompsonJ T ≤
      (CFSG.QuasithinUnique.Setup.Campbell.Hone P).map H.subtype := by
    rw [← thompsonJ_eq_quasithin T, ← map_thompsonJ_sylow P hP]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hL : H ≤ Subgroup.normalizer
      ((CFSG.QuasithinUnique.Setup.Campbell.Hone P).map H.subtype : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro h hh k hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
    exact Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹,
      (inferInstance : (CFSG.QuasithinUnique.Setup.Campbell.Hone P).Normal).conj_mem y hy
        ⟨h, hh⟩, by simp⟩
  exact le_antisymm hone_le (by
    rw [thompsonJ_eq_quasithin H]
    exact CFSG.Quasithin.B6.thompsonJ_le_of_sylow_of_le hT hJL hL)

end Sylow

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
