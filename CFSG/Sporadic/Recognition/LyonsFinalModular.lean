module

public import CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase
public import CFSG.Sporadic.Recognition.LyonsFinalGlue
public import CFSG.Sporadic.Recognition.LyonsFinalMain
public import CFSG.Sporadic.Recognition.LyonsSimsRecognition

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable Subgroup

section Specialisation

theorem lyContains_of_families_modular {R Rfam : List (List (Fin 6 × Bool))}
    (hB : ∀ r ∈ RB, r ∈ R) (hbc : RB5Bound)
    (hM : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
        (subsetOf 6 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1])).index ≤
        9606125)
    (hLy : lyRelCheck R = true) {eEvs : List EEv} {trEvs : List TrEv}
    (hfam : ∀ r ∈ Rfam, FamRel eEvs trEvs r)
    (hcons : ∀ r ∈ R, FreeGroup.mk r ∈ Subgroup.normalClosure
      {x : FreeGroup (Fin 6) | x ∈ Rfam.map FreeGroup.mk}) :
    LyContains := by
  refine lyContains_of_presentation_of_index hB hbc (T := [0, 1]) (by decide)
    hM.1 hM.2 hLy ?_
  intro G _ _ hs hnab hone
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover hone
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  obtain ⟨φ, hφY, hφT, hφK, M, hMtx, k, hk⟩ := D.exists_stage_txW_of_certificates' S
  have hfamG := lift_gOf_of_famRel D S yOK_of_certificate trCheck_eq_true tauOK_eq_true φ hφY
    hφT hφK M hMtx hk hfam
  refine ⟨gOf φ k, ⟨0, gOf_zero_ne_one φ k Ly0.modelChecks_of_certificate⟩, fun r hr => ?_⟩
  have hle : Subgroup.normalClosure {x : FreeGroup (Fin 6) | x ∈ Rfam.map FreeGroup.mk} ≤
      (FreeGroup.lift (gOf φ k)).ker := by
    refine Subgroup.normalClosure_le_normal (fun x hx => ?_)
    simp only [Set.mem_ofPred_eq, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact hfamG w hw
  exact hle (hcons r hr)

theorem S_Ly_leaf_of_families_modular
    {R Rfam : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R) (hbc : RB5Bound)
    (hM : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
        (subsetOf 6 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1])).index ≤
        9606125)
    (hLy : lyRelCheck R = true) {eEvs : List EEv}
    {trEvs : List TrEv} (hfam : ∀ r ∈ Rfam, FamRel eEvs trEvs r)
    (hcons : ∀ r ∈ R, FreeGroup.mk r ∈ Subgroup.normalClosure
      {x : FreeGroup (Fin 6) | x ∈ Rfam.map FreeGroup.mk}) :
    CFSG.GH74.GLS.Stage12.S_Ly_leaf :=
  S_Ly_leaf_of_LyContains (lyContains_of_families_modular hB hbc hM hLy hfam hcons)

theorem LyRecognition_of_families_modular
    {R Rfam : List (List (Fin 6 × Bool))}
    (hB : ∀ r ∈ RB, r ∈ R) (hbc : RB5Bound)
    (hM : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
        (subsetOf 6 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1])).index ≤
        9606125)
    (hLy : lyRelCheck R = true) {eEvs : List EEv} {trEvs : List TrEv}
    (hfam : ∀ r ∈ Rfam, FamRel eEvs trEvs r)
    (hcons : ∀ r ∈ R, FreeGroup.mk r ∈ Subgroup.normalClosure
      {x : FreeGroup (Fin 6) | x ∈ Rfam.map FreeGroup.mk}) :
    LyRecognition :=
  LyRecognition_of_LyContains (lyContains_of_families_modular hB hbc hM hLy hfam hcons)

end Specialisation

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
