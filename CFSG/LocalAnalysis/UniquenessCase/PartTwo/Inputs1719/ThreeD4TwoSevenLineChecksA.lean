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

theorem lineW_check_3 : chunkArr (lineChunks 3) = lineW 3 := by
  decide +kernel

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
