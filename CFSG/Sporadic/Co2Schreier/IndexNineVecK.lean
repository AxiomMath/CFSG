module

public import CFSG.Sporadic.Co2Schreier.Six

public section

namespace CFSG.Sporadic.Co2Schreier.IndexNineVecK

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2

theorem packVec_nil : packVec [] = 0 := by decide +kernel

theorem pv_getD (i : ℕ) : co2PackedVecs[i]! = packVec (co2Rec.vectors.getD i []) := by
  by_cases hi : i < co2Rec.vectors.length
  · rw [co2PackedVecs, getElem!_pos _ i (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp
  · rw [co2PackedVecs, getElem!_neg _ i (by simpa using hi), List.getD_eq_default _ _ (by omega),
      packVec_nil]
    rfl

theorem arr_getD (l : List ℕ) (j : ℕ) : l.toArray[j]! = l.getD j 0 := by
  by_cases hj : j < l.length
  · rw [getElem!_pos _ j (by simpa using hj), List.getD_eq_getElem _ _ hj]
    simp
  · rw [getElem!_neg _ j (by simpa using hj), List.getD_eq_default _ _ (by omega)]
    rfl

theorem sixImage_toArray (l : List ℕ) (k : ℕ) :
    sixImage l.toArray k = packVec (co2Rec.vectors.getD (l.getD (sixIdx k) 0) []) ^^^
      packVec (co2Rec.vectors.getD (l.getD sixAnchorIdx 0) []) := by
  rw [sixImage, pv_getD, pv_getD, arr_getD l, arr_getD l]

@[expose] def eK (j : ℕ) : ℕ :=
  packVec (co2Rec.vectors.getD (sixIdx j) []) ^^^ packVec (co2Rec.vectors.getD sixAnchorIdx [])

@[expose] def tK (c j : ℕ) : ℕ := if c.testBit j then eK j else 0

@[expose] def xor6 (c : ℕ) : ℕ := tK c 0 ^^^ tK c 1 ^^^ tK c 2 ^^^ tK c 3 ^^^ tK c 4 ^^^ tK c 5

theorem idx_lt : ∀ j < 6, sixIdx j < 2300 := by decide +kernel

theorem anchor_lt : sixAnchorIdx < 2300 := by decide +kernel

theorem sixVec_eK (j : Fin 6) : sixVec j = toVecD 22 (eK j) := by
  rw [sixVec, co2Vec_eq_toVecD (idx_lt j j.2), co2Vec_eq_toVecD anchor_lt, pv_getD, pv_getD, eK,
    toVecD_xor]

theorem smul_term (c : ℕ) (j : Fin 6) : toVecD 6 c j • sixVec j = toVecD 22 (tK c j) := by
  rw [sixVec_eK, tK, toVecD_apply]
  split_ifs
  · rw [one_smul]
  · rw [zero_smul, toVecD_zero]

theorem sum_sixVec_xor6 (c : ℕ) :
    ∑ j : Fin 6, toVecD 6 c j • sixVec j = toVecD 22 (xor6 c) := by
  rw [Fin.sum_univ_six]
  simp only [smul_term]
  rw [xor6, toVecD_xor, toVecD_xor, toVecD_xor, toVecD_xor, toVecD_xor]
  rfl

end CFSG.Sporadic.Co2Schreier.IndexNineVecK

end
