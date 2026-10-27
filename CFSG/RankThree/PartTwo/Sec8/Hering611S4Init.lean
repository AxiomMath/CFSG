module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Tab
public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import CFSG.Sporadic.SmallOddCore.J3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.RankThree.Native (validA rep_of_validA enumOK_gens_valid)
open CFSG.RankThree.PartOne (centOKP_enum)
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW)

@[expose] def arrTbl (a : Array ℕ) : Table := a.map UInt32.ofNat

theorem rep_arrTbl {a : Array ℕ} {g : Gp} (hrep : CFSG.Monster.B.Co2.Rep 6156 a g) :
    Rep 6156 (arrTbl a) g := by
  intro i hi
  have h1 := hrep ⟨i, hi⟩
  rw [idx_of_lt g hi]
  have hlt : (g ⟨i, hi⟩ : ℕ) < 2 ^ 32 := lt_of_lt_of_le (g ⟨i, hi⟩).isLt (by norm_num)
  unfold ap arrTbl
  by_cases hia : i < a.size
  · rw [getElem!_pos (a.map UInt32.ofNat) i (by simpa using hia), Array.getElem_map,
      UInt32.toNat_ofNat', ← getElem!_pos a i hia, h1]
    exact Nat.mod_eq_of_lt hlt
  · rw [getElem!_neg (a.map UInt32.ofNat) i (by simpa using hia)]
    rw [getElem!_neg a i hia] at h1
    have h0 : (g ⟨i, hi⟩ : ℕ) = 0 := h1.symm
    change (default : UInt32).toNat = ((g ⟨i, hi⟩ : Fin 6156) : ℕ)
    rw [h0]
    rfl

theorem rep_j3u : Rep 6156 j3OuterTbl j3u :=
  ctuc_j3_involution_centralizer_data.1 0 (by norm_num)

@[expose] def initTblOf (r : ℕ) : Table :=
  if r = 0 then j3PGTbls[0]! else if r = 1 then j3PGTbls[1]! else if r = 2 then j3OuterTbl
  else if r = 3 then arrTbl j3tDGens[0]! else if r = 4 then arrTbl j3tDGens[1]!
  else if r = 5 then arrTbl j3tG else if r = 6 then j3CentTbl 9
  else if r < 12 then j3CentTbl (r + 3) else if r < 16 then arrTbl j3tCAGens[r - 12]!
  else if r = 16 then arrTbl j3tReps[0]! else if r = 17 then arrTbl (evalWA 6156 j3tDGens j3tWu)
  else if r = 18 then arrTbl (evalWA 6156 j3tDGens j3tWv)
  else idT 6156

@[expose] noncomputable def initG (r : ℕ) : Gp :=
  if r = 0 then j3Gen 0 else if r = 1 then j3Gen 1 else if r = 2 then j3u
  else if r = 3 then j3tD 0 else if r = 4 then j3tD 1 else if r = 5 then j3tGPerm
  else if r = 6 then tp 6156 (j3CentTbl 9)
  else if r < 12 then tp 6156 (j3CentTbl (r + 3)) else if r < 16 then
    CFSG.Monster.B.Co2.permOfArr 6156 j3tCAGens[r - 12]!
  else if r = 16 then j3tXA else if r = 17 then evalW j3tD j3tWu
  else if r = 18 then evalW j3tD j3tWv
  else 1

theorem rep_initTblOf
    (r : ℕ) : Rep 6156 (initTblOf r) (initG r) := by
  have hsz : j3PGTbls.size = 2 := rfl
  by_cases h0 : r = 0
  · subst h0
    simpa [initTblOf, initG] using j3_groupData.rep 0 (by rw [hsz]; norm_num)
  by_cases h1 : r = 1
  · subst h1
    simpa [initTblOf, initG] using j3_groupData.rep 1 (by rw [hsz]; norm_num)
  by_cases h2 : r = 2
  · subst h2
    simpa [initTblOf, initG] using rep_j3u
  by_cases h3 : r = 3
  · subst h3
    simp only [initTblOf, initG, if_true, if_false, show (3 : ℕ) ≠ 0 by norm_num,
      show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, j3tD]
    exact rep_arrTbl (rep_of_validA (j3tDGens_valid 0 (by simp [j3tDGens])))
  by_cases h4 : r = 4
  · subst h4
    simp only [initTblOf, initG, if_true, if_false, show (4 : ℕ) ≠ 0 by norm_num,
      show (4 : ℕ) ≠ 1 by norm_num, show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num,
      j3tD]
    exact rep_arrTbl (rep_of_validA (j3tDGens_valid 1 (by simp [j3tDGens])))
  by_cases h5 : r = 5
  · subst h5
    have hG : validA 6156 j3tG = true := by
      have h := j3t_derived_check.2.2.2.2
      simp only [detOK, Bool.and_eq_true] at h
      exact h.1.1.1
    simp only [initTblOf, initG, if_true, if_false, show (5 : ℕ) ≠ 0 by norm_num,
      show (5 : ℕ) ≠ 1 by norm_num, show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num,
      show (5 : ℕ) ≠ 4 by norm_num, j3tGPerm]
    exact rep_arrTbl (rep_of_validA hG)
  by_cases h6 : r = 6
  · subst h6
    simp only [initTblOf, initG, if_true, if_false, show (6 : ℕ) ≠ 0 by norm_num,
      show (6 : ℕ) ≠ 1 by norm_num, show (6 : ℕ) ≠ 2 by norm_num, show (6 : ℕ) ≠ 3 by norm_num,
      show (6 : ℕ) ≠ 4 by norm_num, show (6 : ℕ) ≠ 5 by norm_num]
    exact (ctuc_j3_involution_centralizer_data.1 9 (by norm_num))
  by_cases h12 : r < 12
  · have hr7 : 7 ≤ r := by omega
    simp only [initTblOf, initG, h0, h1, h2, h3, h4, h5, h6, if_false, h12, if_true]
    exact (ctuc_j3_involution_centralizer_data.1 (r + 3) (by omega))
  by_cases h16 : r < 16
  · simp only [initTblOf, initG, h0, h1, h2, h3, h4, h5, h6, if_false, h12, h16, if_true]
    have hk : r - 12 < j3tCAGens.size := by simp [j3tCAGens]; omega
    exact rep_arrTbl (rep_of_validA (enumOK_gens_valid (centOKP_enum j3t_cases_check.1) hk))
  by_cases h17 : r = 16
  · subst h17
    simp only [initTblOf, initG, h0, h1, h2, h3, h4, h5, h6, if_false, h12, h16, if_true]
    exact rep_arrTbl (rep_of_validA (j3tReps_spec (c := 0) (by norm_num)).1)
  by_cases h18 : r = 17
  · subst h18
    simp only [initTblOf, initG, h0, h1, h2, h3, h4, h5, h6, if_false, h12, h16, h17, if_true]
    exact rep_arrTbl (rep_evalWA_j3tD j3tWu)
  by_cases h19 : r = 18
  · subst h19
    simp only [initTblOf, initG, h0, h1, h2, h3, h4, h5, h6, if_false, h12, h16, h17, h18, if_true]
    exact rep_arrTbl (rep_evalWA_j3tD j3tWv)
  · simp only [initTblOf, initG, h0, h1, h2, h3, h4, h5, h6, if_false, h12, h16, h17, h18, h19]
    exact Rep.idT (by norm_num)

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
