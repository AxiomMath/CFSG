module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLCentOverSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbedding.MaxD2 CFSG.RankThree.Native
open Certificates.MaxD2Perm (rGens nGens nGensI repT giT)
open Certificates.MaxD2Heis (mclFiveDataP)

private theorem mcl_check_parts :
    Certificates.MaxD2Perm.checkInv mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHR mclFiveDataP = true ∧
      Certificates.MaxD2Perm.checkN mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHNormal mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHMoves mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHZ mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHExp mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHComm mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHTorus mclFiveDataP = true ∧
      Certificates.MaxD2Heis.checkHCent mclFiveDataP = true ∧
      Certificates.MaxD2Perm.checkMax mclFiveDataP = true := by
  have h := CFSG.AGLEmbeddingD2.mcl_five_check_P
  simpa only [Certificates.MaxD2Heis.checkHeis, Bool.and_eq_true, and_assoc] using h

private theorem mcl_checkInv :
    Certificates.MaxD2Perm.checkInv mclFiveDataP = true :=
  mcl_check_parts.1

private theorem mcl_checkHR :
    Certificates.MaxD2Heis.checkHR mclFiveDataP = true :=
  mcl_check_parts.2.1

private theorem mcl_checkN :
    Certificates.MaxD2Perm.checkN mclFiveDataP = true :=
  mcl_check_parts.2.2.1

private theorem mcl_checkHNormal :
    Certificates.MaxD2Heis.checkHNormal mclFiveDataP = true :=
  mcl_check_parts.2.2.2.1

private theorem mcl_checkHMoves :
    Certificates.MaxD2Heis.checkHMoves mclFiveDataP = true :=
  mcl_check_parts.2.2.2.2.1

private theorem mcl_checkMax :
    Certificates.MaxD2Perm.checkMax mclFiveDataP = true :=
  mcl_check_parts.2.2.2.2.2.2.2.2.2.2

private theorem mcl_hgs :
    ∀ j, TabRep (mclFiveDataP.gT.getD j (idTab 275)) (mclAB.getD j 1) :=
  CFSG.AGLEmbeddingD2.mclFiveDataP_hS

private theorem mcl_hgi :
    ∀ j, TabRep ((giT mclFiveDataP).getD j (idTab 275)) (mclAB.getD j 1)⁻¹ :=
  giT_rep mcl_hgs mcl_checkInv

theorem gsub_mclAB : Gsub (D := mclFiveDataP) mclAB = mcl275P := by
  show Subgroup.closure {g | g ∈ [mcl275A, mcl275B]} = mcl275P
  exact CFSG.AGLEmbeddingD2.mclP_closure_eq

theorem mcl_rep_u :
    TabRep (rGens mclFiveDataP)[0]! mclU5 :=
  rep_u (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi

theorem mcl_rep_v :
    TabRep (rGens mclFiveDataP)[1]! mclV5 :=
  rep_v (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi

theorem mclR5_eq : mclR5 = Subgroup.closure {mclU5, mclV5} :=
  Rsub_eq_closure

theorem mclR5_le : mclR5 ≤ mcl275P := by
  rw [← gsub_mclAB]
  exact Rsub_le_Gsub

theorem card_mclR5 :
    Nat.card mclR5 = 125 := by
  have h := card_RH (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi mcl_checkHR
  rw [show mclFiveDataP.p = 5 from rfl] at h
  norm_num at h
  exact h

theorem mclN5_eq : mclN5 = Subgroup.closure {g | g ∈ mclNGens5} := rfl

theorem mclN5_le : mclN5 ≤ mcl275P := by
  rw [← gsub_mclAB]
  exact Nsub_le_Gsub

theorem mclN5_le_normalizer :
    mclN5 ≤ Subgroup.normalizer (mclR5 : Set (Equiv.Perm (Fin 275))) :=
  N_le_normalizer_H (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi mcl_checkHR
    mcl_checkHNormal

theorem normalizer_inf_mcl275P :
    Subgroup.normalizer (mclR5 : Set (Equiv.Perm (Fin 275))) ⊓ mcl275P = mclN5 := by
  have hlen : mclAB.length = mclFiveDataP.gT.size := rfl
  have hcard : Nat.card (Gsub (D := mclFiveDataP) mclAB) = mclFiveDataP.gOrder := by
    rw [gsub_mclAB]
    exact CFSG.Sporadic.Schreier.card_mclP
  have h := normalizer_inf_eq_H (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi hlen
    hcard mcl_checkHR mcl_checkN mcl_checkHNormal mcl_checkHMoves mcl_checkMax
  rw [gsub_mclAB] at h
  exact h

theorem card_mclN5 :
    Nat.card mclN5 = 3000 := by
  have h := card_N (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi mcl_checkN
  rw [show mclFiveDataP.nOrder = 3000 from rfl] at h
  exact h

theorem mcl_rep_nGens :
    ∀ j, TabRep ((nGens mclFiveDataP).getD j (idTab 275)) (mclNGens5.getD j 1) :=
  rep_map_words mclAB mclFiveDataP.gT (giT mclFiveDataP) mcl_hgs mcl_hgi mclFiveDataP.nW

theorem mcl_rep_nGensI :
    ∀ j, TabRep ((nGensI mclFiveDataP).getD j (idTab 275)) (mclNGens5.getD j 1)⁻¹ :=
  nGensI_rep (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi
    (invsOK_of_checkHNormal mcl_checkHNormal)

theorem mcl_rep_repT :
    ∀ i, TabRep ((repT mclFiveDataP).getD i (idTab 275)) (mclRep5 i) :=
  repT_rep (D := mclFiveDataP) (S := mclAB) mcl_hgs mcl_hgi

theorem mclRep5_mem (i : ℕ) : mclRep5 i ∈ mcl275P := by
  rw [← gsub_mclAB]
  by_cases hi : i < (repElts mclFiveDataP mclAB).length
  · exact repElts_mem (getD_mem_of_lt hi 1)
  · unfold mclRep5
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Subgroup.one_mem _

theorem mclH5_mem (k : ℕ) : mclH5 k ∈ mclN5 := by
  rw [mclN5_eq]
  unfold mclH5
  by_cases hk : k < (Certificates.McLFivePairs.conjWords.map (wordVal mclNGens5)).length
  · obtain ⟨w, -, hw⟩ := List.mem_map.1 (getD_mem_of_lt hk 1)
    rw [← hw]
    exact wordVal_mem mclNGens5 _ (fun g hg => Subgroup.subset_closure hg) w
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Subgroup.one_mem _

theorem mcl_exists_dcoset :
    ∀ y ∈ mcl275P, ∃ i ≤ 113, ∃ a ∈ mclN5, ∃ b ∈ mclN5, y = a * mclRep5 i * b := by
  have hcard : Nat.card (Gsub (D := mclFiveDataP) mclAB) = mclFiveDataP.gOrder := by
    rw [gsub_mclAB]
    exact CFSG.Sporadic.Schreier.card_mclP
  have h := exists_dcoset_of_checkHeis (D := mclFiveDataP) (S := mclAB) mcl_hgs hcard
    (CFSG.AGLEmbeddingD2.mcl_five_check_P)
  rw [gsub_mclAB, mcl_repW_length] at h
  intro y hy
  obtain ⟨i, hi, a, ha, b, hb, hyab⟩ := h y hy
  exact ⟨i, hi, a, ha, b, hb, hyab⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
