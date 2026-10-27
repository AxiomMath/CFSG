module

public import CFSG.Sporadic.Schreier.TitsCert
public import CFSG.Sporadic.Schreier.TitsLocalCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def titsKappa (j : Fin 8775) : Fin 2925 := finPt 2925 titsKappaArr[(j : ℕ)]!

@[expose] def titsAStar (i : ℕ) : Equiv.Perm (Fin 2925) := permOfArr 2925 titsAStarArrs[i]!

@[expose] def titsDFlagCmp (j : ℕ) : Equiv.Perm (Fin 8775) := permOfArr 8775 titsDFlagStored[j]!

@[expose] def titsDStarCmp (j : ℕ) : Equiv.Perm (Fin 2925) := permOfArr 2925 titsDStarStored[j]!

@[expose] def titsDFlag (j : ℕ) : Equiv.Perm (Fin 8775) :=
  tcomm (wordIn 4 titsP (titsU j)) (wordIn 4 titsP (titsV j))

@[expose] def titsDStar (j : ℕ) : Equiv.Perm (Fin 2925) :=
  tcomm (wordIn 4 titsAStar (titsU j)) (wordIn 4 titsAStar (titsV j))

@[expose] def titsTFlag (i : ℕ) : Equiv.Perm (Fin 8775) :=
  strongOf 2 titsDFlag titsDerivedDerivations i

@[expose] def titsTStar (i : ℕ) : Equiv.Perm (Fin 2925) :=
  strongOf 2 titsDStar titsDerivedDerivations i

@[expose] def titsWordGroup (ws : List (List ℤ)) : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure {g | ∃ w ∈ ws, wordIn 13 titsT w = g}

@[expose] def titsH : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsHWords

@[expose] def titsS : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsSWords

@[expose] def titsN : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsNWords

@[expose] def titsJ : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsJWords

@[expose] def titsK : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsKWords

@[expose] def titsR : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsRWords

theorem titsHArrs_size :
    titsHArrs.size = 9 := titsLocalData_check.2.2.2.2.1

theorem titsSArrs_size :
    titsSArrs.size = 9 := titsLocalData_check.2.2.2.2.2.1

theorem titsNArrs_size :
    titsNArrs.size = 10 := titsLocalData_check.2.2.2.2.2.2.1

theorem titsJArrs_size :
    titsJArrs.size = 9 := titsLocalData_check.2.2.2.2.2.2.2.1

theorem titsKArrs_size :
    titsKArrs.size = 7 := titsLocalData_check.2.2.2.2.2.2.2.2.1

theorem titsRArrs_size :
    titsRArrs.size = 8 := titsLocalData_check.2.2.2.2.2.2.2.2.2.1

@[expose] def titsQH : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsHArrs 3 (by rw [titsHArrs_size]; norm_num)
    (finList 1755 titsHBase) (by decide) (wordsArr 3 9 titsHDerivations)

@[expose] def titsQS : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsSArrs 3 (by rw [titsSArrs_size]; norm_num)
    (finList 1755 titsSBase) (by decide) (wordsArr 3 9 titsSDerivations)

@[expose] def titsQN : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsNArrs 4 (by rw [titsNArrs_size]; norm_num)
    (finList 1755 titsNBase) (by decide) (wordsArr 4 10 titsNDerivations)

@[expose] def titsQJ : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsJArrs 4 (by rw [titsJArrs_size]; norm_num)
    (finList 1755 titsJBase) (by decide) (wordsArr 4 9 titsJDerivations)

@[expose] def titsQK : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsKArrs 2 (by rw [titsKArrs_size]; norm_num)
    (finList 1755 titsKBase) (by decide) (wordsArr 2 7 titsKDerivations)

@[expose] def titsQR : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsRArrs 3 (by rw [titsRArrs_size]; norm_num)
    (finList 1755 titsRBase) (by decide) (wordsArr 3 8 titsRDerivations)

@[expose] def titsZ : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsCenterWord

@[expose] def titsX : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsXWord

@[expose] def titsY : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsYWord

@[expose] def titsFiveFlagList : List (Fin 8775) := finList 8775 titsFiveFlags

@[expose] def titsThreeFlagList : List (Fin 8775) := finList 8775 titsThreeFlags

@[expose] def titsOtherRepList : List (Fin 2925) := finList 2925 titsOtherReps

@[expose] def titsOtherMerge (l : ℕ) : List (Fin 2 × Fin 2925 × Fin 2925) :=
  (titsOtherMergeVals l).map fun m => (finPt 2 m.1, finPt 2925 m.2.1, finPt 2925 m.2.2)

theorem titsQD_strong_get
    (j : Fin titsQD.strongCount) : titsQD.strong.get j = titsT j :=
  RawSchreierDatum.ofArrays_strong_get j

theorem wordIn_titsT_mem_titsD
    (w : List ℤ) : wordIn 13 titsT w ∈ titsD :=
  wordIn_mem (fun _ hi => titsT_mem_titsD hi) w

theorem titsWordGroup_le_titsD
    (ws : List (List ℤ)) : titsWordGroup ws ≤ titsD := by
  rw [titsWordGroup, Subgroup.closure_le]
  rintro _ ⟨w, -, rfl⟩
  exact wordIn_titsT_mem_titsD w

theorem titsH_le_titsD : titsH ≤ titsD :=
  titsWordGroup_le_titsD _

theorem titsS_le_titsD : titsS ≤ titsD :=
  titsWordGroup_le_titsD _

theorem titsN_le_titsD : titsN ≤ titsD :=
  titsWordGroup_le_titsD _

theorem titsJ_le_titsD : titsJ ≤ titsD :=
  titsWordGroup_le_titsD _

theorem titsK_le_titsD : titsK ≤ titsD :=
  titsWordGroup_le_titsD _

theorem titsR_le_titsD : titsR ≤ titsD :=
  titsWordGroup_le_titsD _

theorem titsZ_mem_titsD : titsZ ∈ titsD :=
  wordIn_titsT_mem_titsD _

theorem titsX_mem_titsD : titsX ∈ titsD :=
  wordIn_titsT_mem_titsD _

theorem titsY_mem_titsD : titsY ∈ titsD :=
  wordIn_titsT_mem_titsD _

theorem titsKappa_rep
    (j : Fin 8775) : (titsKappa j : ℕ) = titsKappaArr[(j : ℕ)]! :=
  finPt_val (of_decide_eq_true
    (allLt_spec titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j.2))

theorem AT_Tits_local_certificate_data :
    titsQD.strongCount = 13 ∧ (∀ j : Fin titsQD.strongCount, titsQD.strong.get j = titsT j) ∧
    titsDerivedDerivations.length = 11 ∧
    titsOriginalSha = "42305a5cb1bff4c70a559900b823541145797391d27937a4ba1861bb9fab10e1" ∧
    (∀ j : Fin 8775, (titsKappa j : ℕ) = titsKappaArr[(j : ℕ)]!) ∧
    (∀ i < 4, Rep 2925 titsAStarArrs[i]! (titsAStar i)) ∧
    (∀ j < 2, Rep 8775 titsDFlagStored[j]! (titsDFlagCmp j) ∧
      Rep 2925 titsDStarStored[j]! (titsDStarCmp j)) ∧
    (titsLocalWords.all fun ws => ws.all (lettersOK 13)) = true ∧
    titsH ≤ titsD ∧ titsS ≤ titsD ∧ titsN ≤ titsD ∧ titsJ ≤ titsD ∧ titsK ≤ titsD ∧
    titsR ≤ titsD ∧ titsZ ∈ titsD ∧ titsX ∈ titsD ∧ titsY ∈ titsD ∧
    (titsQH.originalCount, titsQH.strongCount) = titsHCounts ∧
    (titsQS.originalCount, titsQS.strongCount) = titsSCounts ∧
    (titsQN.originalCount, titsQN.strongCount) = titsNCounts ∧
    (titsQJ.originalCount, titsQJ.strongCount) = titsJCounts ∧
    (titsQK.originalCount, titsQK.strongCount) = titsKCounts ∧
    (titsQR.originalCount, titsQR.strongCount) = titsRCounts ∧
    titsQH.base.toList.map Fin.val = titsHBase ∧ titsQS.base.toList.map Fin.val = titsSBase ∧
    titsQN.base.toList.map Fin.val = titsNBase ∧ titsQJ.base.toList.map Fin.val = titsJBase ∧
    titsQK.base.toList.map Fin.val = titsKBase ∧ titsQR.base.toList.map Fin.val = titsRBase ∧
    titsFiveFlags.length = 5 ∧ titsThreeFlags.length = 3 ∧
    titsProvenance.length = titsRWords.length ∧ titsRWords.length = 3 ∧
    titsOtherReps.length = 6 ∧ titsOtherSizes.length = 6 ∧
    (∀ l < 5, (titsOtherMerge l).length = 2923) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, lR, -⟩ := titsLocalChains_check
  refine ⟨by simp [titsQD, RawSchreierDatum.ofArrays_strongCount, titsDerivedArrs_size],
    titsQD_strong_get, rfl, rfl, titsKappa_rep, fun i hi => ?_, fun j hj => ⟨?_, ?_⟩,
    titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, titsH_le_titsD,
    titsS_le_titsD, titsN_le_titsD, titsJ_le_titsD, titsK_le_titsD, titsR_le_titsD,
    titsZ_mem_titsD, titsX_mem_titsD, titsY_mem_titsD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, rfl, rfl, ?_, lR, rfl, rfl, fun l _ => by simp [titsOtherMerge, titsOtherMergeVals]⟩
  · exact rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.2.1]; exact hi)
  · exact rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.2.2.1]; exact hj)
  · exact rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.2.2.2.1]; exact hj)
  · show (3, titsHArrs.size) = titsHCounts
    rw [titsHArrs_size]
    rfl
  · show (3, titsSArrs.size) = titsSCounts
    rw [titsSArrs_size]
    rfl
  · show (4, titsNArrs.size) = titsNCounts
    rw [titsNArrs_size]
    rfl
  · show (4, titsJArrs.size) = titsJCounts
    rw [titsJArrs_size]
    rfl
  · show (2, titsKArrs.size) = titsKCounts
    rw [titsKArrs_size]
    rfl
  · show (3, titsRArrs.size) = titsRCounts
    rw [titsRArrs_size]
    rfl
  · rw [titsQH, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [titsQS, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [titsQN, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [titsQJ, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [titsQK, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [titsQR, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rfl

end CFSG.Sporadic.Schreier.Tits
