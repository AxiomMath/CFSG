module

public import CFSG.Sporadic.Recognition.LyonsFinalModular
public import Certificates.Certificate6114
public import Certificates.Certificate6115
public import Certificates.Certificate6116
public import Certificates.Certificate6117
public import Certificates.Certificate6118

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem rb5Bound_holds : RB5Bound :=
  Certificates.certificate6114

theorem dist2_mem_normalClosure :
    ∀ r ∈ dist2Relators, FreeGroup.mk r ∈ Subgroup.normalClosure
      {x : FreeGroup (Fin 6) |
        x ∈ ((kkRel :: trRel dist2TrEv :: dist2EEvs.map eRelOf) ++ dist2BWords).map FreeGroup.mk} :=
  Certificates.certificate6115

theorem rb_mem_modularR :
    ∀ r ∈ RB, r ∈ modularR Rcore107 modularD :=
  Certificates.certificate6116.1

theorem famRel_core107 :
    ∀ r ∈ Rcore107 ++ modularLearned ++ dist2BWords, FamRel eEvCore trEvCore r :=
  Certificates.certificate6116.2

theorem lyRelCheck_modularR_eq_true :
    lyRelCheck (modularR Rcore107 modularD) = true :=
  Certificates.certificate6117

theorem index_cd_modularR :
    (CFSG.CosetTable.genSub
        {r : FreeGroup (Fin 6) | r ∈ (modularR Rcore107 modularD).map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf 6 [0, 1])).FiniteIndex ∧
      (CFSG.CosetTable.genSub
        {r : FreeGroup (Fin 6) | r ∈ (modularR Rcore107 modularD).map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf 6 [0, 1])).index ≤ 9606125 :=
  Certificates.certificate6118

theorem modularD_eq_dist2Relators : modularD = dist2Relators := by decide

theorem kkRel_mem_Rcore107 : kkRel ∈ Rcore107 := by decide

theorem eRelOf_mem_Rcore107 : ∀ e ∈ dist2EEvs, eRelOf e ∈ Rcore107 := by decide

theorem trRel_dist2TrEv_mem_Rcore107 : trRel dist2TrEv ∈ Rcore107 := by decide

theorem modularR_mem_normalClosure :
    ∀ r ∈ modularR Rcore107 modularD, FreeGroup.mk r ∈ Subgroup.normalClosure
      {x : FreeGroup (Fin 6) |
        x ∈ (Rcore107 ++ modularLearned ++ dist2BWords).map FreeGroup.mk} := by
  intro r hr
  simp only [modularR, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · exact Subgroup.subset_normalClosure (List.mem_map_of_mem (by simp [hr]))
  · exact Subgroup.subset_normalClosure (List.mem_map_of_mem (by simp [hr]))
  · rw [modularD_eq_dist2Relators] at hr
    refine Subgroup.normalClosure_mono ?_ (dist2_mem_normalClosure r hr)
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    refine List.mem_map_of_mem ?_
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hw
    rcases hw with (rfl | rfl | ⟨e, he, rfl⟩) | hw
    · exact List.mem_append_left _ (List.mem_append_left _ kkRel_mem_Rcore107)
    · exact List.mem_append_left _ (List.mem_append_left _ trRel_dist2TrEv_mem_Rcore107)
    · exact List.mem_append_left _ (List.mem_append_left _ (eRelOf_mem_Rcore107 e he))
    · exact List.mem_append_right _ hw

section Final

theorem s_Ly_leaf :
    CFSG.GH74.GLS.Stage12.S_Ly_leaf :=
  S_Ly_leaf_of_families_modular (R := modularR Rcore107 modularD)
    (Rfam := Rcore107 ++ modularLearned ++ dist2BWords) (eEvs := eEvCore) (trEvs := trEvCore)
    rb_mem_modularR rb5Bound_holds index_cd_modularR
    lyRelCheck_modularR_eq_true famRel_core107 modularR_mem_normalClosure

theorem lyRecognition :
    LyRecognition :=
  LyRecognition_of_families_modular (R := modularR Rcore107 modularD)
    (Rfam := Rcore107 ++ modularLearned ++ dist2BWords) (eEvs := eEvCore) (trEvs := trEvCore)
    rb_mem_modularR rb5Bound_holds index_cd_modularR
    lyRelCheck_modularR_eq_true famRel_core107 modularR_mem_normalClosure

end Final

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
