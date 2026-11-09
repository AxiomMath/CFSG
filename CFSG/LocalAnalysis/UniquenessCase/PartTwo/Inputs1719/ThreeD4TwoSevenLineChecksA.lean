module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenLineData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Quasithin.H13.D42

theorem lineW_check_0 : chunkArr (lineChunks 0) = lineW 0 := by
  decide +kernel

theorem lineW_check_1 : chunkArr (lineChunks 1) = lineW 1 := by
  decide +kernel

theorem lineW_check_2 : chunkArr (lineChunks 2) = lineW 2 := by
  decide +kernel

private def lineW3_p1 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 1, 6, 0, 0, 1, 3, 5, 4, 0, 0, 0, 0, 1, 2, 5, 1, 3,
    2, 0, 0, 1, 3, 4, 7, 7, 3, 0, 0, 1, 2, 4, 3, 5, 3, 1, 7, 5, 4, 7, 2, 1, 7, 1, 6, 4, 0, 1, 5,
    3, 3] : Array ℕ).map GF8.ofNat'

private def lineW3_p2 : Array GF8 :=
  (#[0, 0, 1, 2, 4, 3, 5, 3, 1, 6, 4, 0, 1, 5, 2, 5, 0, 0, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 1, 2, 6,
    1, 0, 0, 0, 1, 0, 4, 2, 0, 0, 1, 1, 4, 6, 7, 2, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1,
    1, 2] : Array ℕ).map GF8.ofNat'

private def lineW3_p3 : Array GF8 :=
  (#[1, 7, 4, 6, 3, 1, 4, 4, 0, 1, 1, 5, 7, 0, 6, 1, 0, 0, 1, 3, 5, 4, 1, 6, 0, 0, 0, 1, 0, 5, 2,
    4, 0, 0, 0, 0, 1, 3, 6, 5, 0, 0, 0, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0,
    0, 1] : Array ℕ).map GF8.ofNat'

private theorem lineW3_s3 : chunkArr ((lineChunks 3).drop 3) = lineW3_p3 := by
  decide +kernel

private theorem lineW3_s2 :
    mulArr (wordArr ((lineChunks 3).getD 2 [])) lineW3_p3 = lineW3_p2 := by
  decide +kernel

private theorem lineW3_s1 :
    mulArr (wordArr ((lineChunks 3).getD 1 [])) lineW3_p2 = lineW3_p1 := by
  decide +kernel

private theorem lineW3_s0 :
    mulArr (wordArr ((lineChunks 3).getD 0 [])) lineW3_p1 = lineW 3 := by
  decide +kernel

theorem lineW_check_3 : chunkArr (lineChunks 3) = lineW 3 := by
  have e : lineChunks 3 = (lineChunks 3).getD 0 [] :: (lineChunks 3).getD 1 [] ::
      (lineChunks 3).getD 2 [] :: (lineChunks 3).drop 3 := rfl
  have hc : ∀ (c : List ℕ) (cs : List (List ℕ)),
      chunkArr (c :: cs) = mulArr (wordArr c) (chunkArr cs) := by
    intro c cs
    unfold chunkArr
    rw [List.foldr_cons]
  rw [e, hc, hc, hc, lineW3_s3, lineW3_s2, lineW3_s1, lineW3_s0]

theorem lineRel_check_0 : mulArr (lineW 0) (lineQ 0) =
      mulArr (powArr (lineQ 0) (lineExp 0)) (lineW 0) ∧
    mulArr (lineW 0) (mulArr (lineW 0) (lineW 0)) = oneArr ∧ lineW 0 ≠ oneArr ∧
    (lineW 0).size = 64 := by
  decide +kernel

theorem lineRel_check_1 : mulArr (lineW 1) (lineQ 1) =
      mulArr (powArr (lineQ 1) (lineExp 1)) (lineW 1) ∧
    mulArr (lineW 1) (mulArr (lineW 1) (lineW 1)) = oneArr ∧ lineW 1 ≠ oneArr ∧
    (lineW 1).size = 64 := by
  decide +kernel

theorem lineRel_check_2 : mulArr (lineW 2) (lineQ 2) =
      mulArr (powArr (lineQ 2) (lineExp 2)) (lineW 2) ∧
    mulArr (lineW 2) (mulArr (lineW 2) (lineW 2)) = oneArr ∧ lineW 2 ≠ oneArr ∧
    (lineW 2).size = 64 := by
  decide +kernel

theorem lineRel_check_3 : mulArr (lineW 3) (lineQ 3) =
      mulArr (powArr (lineQ 3) (lineExp 3)) (lineW 3) ∧
    mulArr (lineW 3) (mulArr (lineW 3) (lineW 3)) = oneArr ∧ lineW 3 ≠ oneArr ∧
    (lineW 3).size = 64 := by
  decide +kernel

theorem lineQ_check_0 : mulArr e49ArrH (powArr e49ArrZ 0) = lineQ 0 := by
  decide +kernel

theorem lineQ_check_1 : mulArr e49ArrH (powArr e49ArrZ 1) = lineQ 1 := by
  decide +kernel

theorem lineQ_check_2 : mulArr e49ArrH (powArr e49ArrZ 2) = lineQ 2 := by
  decide +kernel

theorem lineQ_check_3 : mulArr e49ArrH (powArr e49ArrZ 3) = lineQ 3 := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines
