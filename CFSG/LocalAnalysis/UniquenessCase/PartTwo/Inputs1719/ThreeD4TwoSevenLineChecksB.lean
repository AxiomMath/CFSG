module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenLineData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Quasithin.H13.D42

theorem lineW_check_4 : chunkArr (lineChunks 4) = lineW 4 := by
  decide +kernel

private def lineW5_p1 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 1, 4, 2,
    0, 0, 0, 0, 1, 0, 6, 4, 1, 0, 0, 1, 4, 6, 5, 6, 7, 0, 1, 0, 2, 4, 7, 3, 5, 1, 2, 6, 1, 0, 5,
    3, 5] : Array ℕ).map GF8.ofNat'

private def lineW5_p2 : Array GF8 :=
  (#[0, 0, 1, 4, 6, 5, 6, 7, 1, 2, 6, 1, 0, 5, 2, 7, 1, 2, 6, 1, 0, 5, 3, 5, 0, 0, 0, 0, 1, 4, 2,
    0, 0, 0, 0, 1, 0, 6, 4, 1, 0, 1, 0, 2, 4, 7, 3, 4, 0, 1, 0, 2, 4, 7, 3, 5, 0, 0, 0, 0, 0, 1,
    0, 6] : Array ℕ).map GF8.ofNat'

private def lineW5_p3 : Array GF8 :=
  (#[1, 1, 6, 7, 7, 7, 6, 1, 0, 1, 1, 3, 5, 6, 2, 5, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 4,
    5, 0, 0, 0, 0, 1, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 7, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0,
    0, 1] : Array ℕ).map GF8.ofNat'

private theorem lineW5_s3 : chunkArr ((lineChunks 5).drop 3) = lineW5_p3 := by
  decide +kernel

private theorem lineW5_s2 :
    mulArr (wordArr ((lineChunks 5).getD 2 [])) lineW5_p3 = lineW5_p2 := by
  decide +kernel

private theorem lineW5_s1 :
    mulArr (wordArr ((lineChunks 5).getD 1 [])) lineW5_p2 = lineW5_p1 := by
  decide +kernel

private theorem lineW5_s0 :
    mulArr (wordArr ((lineChunks 5).getD 0 [])) lineW5_p1 = lineW 5 := by
  decide +kernel

theorem lineW_check_5 : chunkArr (lineChunks 5) = lineW 5 := by
  have e : lineChunks 5 = (lineChunks 5).getD 0 [] :: (lineChunks 5).getD 1 [] ::
      (lineChunks 5).getD 2 [] :: (lineChunks 5).drop 3 := rfl
  have hc : ∀ (c : List ℕ) (cs : List (List ℕ)),
      chunkArr (c :: cs) = mulArr (wordArr c) (chunkArr cs) := by
    intro c cs
    unfold chunkArr
    rw [List.foldr_cons]
  rw [e, hc, hc, hc, lineW5_s3, lineW5_s2, lineW5_s1, lineW5_s0]

private def lineW6_p1 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 6, 4,
    0, 0, 0, 0, 1, 0, 2, 6, 1, 0, 0, 1, 6, 2, 7, 2, 3, 0, 1, 0, 4, 6, 3, 5, 7, 1, 4, 2, 1, 0, 7,
    5, 7] : Array ℕ).map GF8.ofNat'

private def lineW6_p2 : Array GF8 :=
  (#[0, 0, 1, 6, 2, 7, 2, 3, 1, 4, 2, 1, 0, 7, 4, 3, 1, 4, 2, 1, 0, 7, 5, 7, 0, 0, 0, 0, 1, 6, 4,
    0, 0, 0, 0, 1, 0, 2, 6, 1, 0, 1, 0, 4, 6, 3, 5, 6, 0, 1, 0, 4, 6, 3, 5, 7, 0, 0, 0, 0, 0, 1,
    0, 2] : Array ℕ).map GF8.ofNat'

private def lineW6_p3 : Array GF8 :=
  (#[1, 6, 2, 2, 7, 1, 4, 2, 0, 1, 1, 6, 2, 0, 7, 1, 0, 0, 1, 2, 4, 3, 2, 6, 0, 0, 0, 1, 0, 4, 6,
    6, 0, 0, 0, 0, 1, 2, 4, 3, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0,
    0, 1] : Array ℕ).map GF8.ofNat'

private theorem lineW6_s3 : chunkArr ((lineChunks 6).drop 3) = lineW6_p3 := by
  decide +kernel

private theorem lineW6_s2 :
    mulArr (wordArr ((lineChunks 6).getD 2 [])) lineW6_p3 = lineW6_p2 := by
  decide +kernel

private theorem lineW6_s1 :
    mulArr (wordArr ((lineChunks 6).getD 1 [])) lineW6_p2 = lineW6_p1 := by
  decide +kernel

private theorem lineW6_s0 :
    mulArr (wordArr ((lineChunks 6).getD 0 [])) lineW6_p1 = lineW 6 := by
  decide +kernel

theorem lineW_check_6 : chunkArr (lineChunks 6) = lineW 6 := by
  have e : lineChunks 6 = (lineChunks 6).getD 0 [] :: (lineChunks 6).getD 1 [] ::
      (lineChunks 6).getD 2 [] :: (lineChunks 6).drop 3 := rfl
  have hc : ∀ (c : List ℕ) (cs : List (List ℕ)),
      chunkArr (c :: cs) = mulArr (wordArr c) (chunkArr cs) := by
    intro c cs
    unfold chunkArr
    rw [List.foldr_cons]
  rw [e, hc, hc, hc, lineW6_s3, lineW6_s2, lineW6_s1, lineW6_s0]

theorem lineW_check_7 : chunkArr (lineChunks 7) = lineW 7 := by
  decide +kernel

theorem lineRel_check_4 : mulArr (lineW 4) (lineQ 4) =
      mulArr (powArr (lineQ 4) (lineExp 4)) (lineW 4) ∧
    mulArr (lineW 4) (mulArr (lineW 4) (lineW 4)) = oneArr ∧ lineW 4 ≠ oneArr ∧
    (lineW 4).size = 64 := by
  decide +kernel

theorem lineRel_check_5 : mulArr (lineW 5) (lineQ 5) =
      mulArr (powArr (lineQ 5) (lineExp 5)) (lineW 5) ∧
    mulArr (lineW 5) (mulArr (lineW 5) (lineW 5)) = oneArr ∧ lineW 5 ≠ oneArr ∧
    (lineW 5).size = 64 := by
  decide +kernel

theorem lineRel_check_6 : mulArr (lineW 6) (lineQ 6) =
      mulArr (powArr (lineQ 6) (lineExp 6)) (lineW 6) ∧
    mulArr (lineW 6) (mulArr (lineW 6) (lineW 6)) = oneArr ∧ lineW 6 ≠ oneArr ∧
    (lineW 6).size = 64 := by
  decide +kernel

theorem lineRel_check_7 : mulArr (lineW 7) (lineQ 7) =
      mulArr (powArr (lineQ 7) (lineExp 7)) (lineW 7) ∧
    mulArr (lineW 7) (mulArr (lineW 7) (lineW 7)) = oneArr ∧ lineW 7 ≠ oneArr ∧
    (lineW 7).size = 64 := by
  decide +kernel

theorem lineQ_check_4 : mulArr e49ArrH (powArr e49ArrZ 4) = lineQ 4 := by
  decide +kernel

theorem lineQ_check_5 : mulArr e49ArrH (powArr e49ArrZ 5) = lineQ 5 := by
  decide +kernel

theorem lineQ_check_6 : mulArr e49ArrH (powArr e49ArrZ 6) = lineQ 6 := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines
