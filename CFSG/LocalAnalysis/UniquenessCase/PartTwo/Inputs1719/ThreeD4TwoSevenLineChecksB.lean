module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenLineData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Quasithin.H13.D42

theorem lineW_check_4 : chunkArr (lineChunks 4) = lineW 4 := by
  decide +kernel

theorem lineW_check_5 : chunkArr (lineChunks 5) = lineW 5 := by
  decide +kernel

theorem lineW_check_6 : chunkArr (lineChunks 6) = lineW 6 := by
  decide +kernel

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
