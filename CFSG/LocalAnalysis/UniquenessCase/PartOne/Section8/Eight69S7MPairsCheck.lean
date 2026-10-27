module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsLocal
public import Certificates.Certificate1567001
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsTab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbedding.MaxD2 CFSG.RankThree.Native Certificates.McLFivePairs
open Certificates.MaxD2Perm (rGens nGens nGensI repT)
open Certificates.MaxD2Heis (mclFiveDataP)

abbrev mclB0T : Array Tab :=
  pairGens (rGens mclFiveDataP)[0]! (rGens mclFiveDataP)[1]!
    ((repT mclFiveDataP).getD excIdx (idTab 275))

abbrev mclHT5 : Array Tab := conjTabs (nGens mclFiveDataP) (nGensI mclFiveDataP)

abbrev mclBT5 : Array (Array Tab) := mclHT5.map (blockGens mclB0T)

theorem mcl_pairs_check_spec :
    pairWords.map (·.1) = (List.range 114).filter (fun i => i != 0 && i != excIdx) ∧
    (∀ e ∈ pairWords,
      pairOK (rGens mclFiveDataP)[0]! (rGens mclFiveDataP)[1]! (repT mclFiveDataP) e = true) ∧
    hasInv ((repT mclFiveDataP).getD excIdx (idTab 275)) = true ∧ gensOK mclB0T = true ∧
    mclHT5.size = 3 ∧ (∀ k < 3, hasInv (mclHT5.getD k (idTab 275)) = true) ∧
    (∀ k < 3, gensOK (mclBT5.getD k #[]) = true) ∧
    actWords.map (fun e => (e.1, e.2.1)) = actIndex ∧
    (∀ e ∈ actWords, actOK mclBT5 (nGens mclFiveDataP) e = true) ∧
    joinWords.map (fun e => (e.1, e.2.1)) = joinIndex ∧
    (∀ e ∈ joinWords, joinOK mclBT5 e = true) ∧
    chainOK mclB0T = true := by
  have h := Certificates.certificate1567001
  simp only [check, Bool.and_eq_true, List.all_eq_true, allBelow_eq_true, beq_iff_eq,
    and_assoc] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem rep_mclB0T :
    ∀ j, TabRep (mclB0T.getD j (idTab 275)) (mclB0Gens.getD j 1) := by
  have hInv95 : hasInv ((repT mclFiveDataP).getD excIdx (idTab 275)) = true :=
    mcl_pairs_check_spec.2.2.1
  exact rep_pairGens mcl_rep_u mcl_rep_v (mcl_rep_repT 95) hInv95

theorem rep_mclHT5 :
    ∀ k, TabRep (mclHT5.getD k (idTab 275)) (mclH5 k) := by
  exact rep_map_words mclNGens5 (nGens mclFiveDataP) (nGensI mclFiveDataP)
    mcl_rep_nGens mcl_rep_nGensI conjWords

theorem rep_mclBT5
    {k : ℕ} (hk : k < 3) :
    ∀ j, TabRep ((mclBT5.getD k #[]).getD j (idTab 275)) ((mclBGens5 k).getD j 1) := by
  have hsize : mclHT5.size = 3 := mcl_pairs_check_spec.2.2.2.2.1
  have hInv : ∀ k < 3, hasInv (mclHT5.getD k (idTab 275)) = true :=
    mcl_pairs_check_spec.2.2.2.2.2.1
  have hk' : k < mclHT5.size := by rw [hsize]; exact hk
  have hget : mclBT5.getD k #[] = blockGens mclB0T (mclHT5.getD k (idTab 275)) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hk',
      Option.map_some, Option.getD_some]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some]
  have hlen : mclB0T.size = mclB0Gens.length := by decide
  intro j
  rw [hget]
  exact rep_blockGens rep_mclB0T hlen (rep_mclHT5 k) (hInv k hk) j

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
