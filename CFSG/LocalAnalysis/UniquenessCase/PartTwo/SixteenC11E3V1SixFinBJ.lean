module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinTabs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem sixChk4_part0 : (List.range' 0 19).all (sixChk4Row sixAdjL) = true := by
  decide +kernel

private theorem sixChk4_part1 : (List.range' 19 19).all (sixChk4Row sixAdjL) = true := by
  decide +kernel

private theorem sixChk4_part2 : (List.range' 38 19).all (sixChk4Row sixAdjL) = true := by
  decide +kernel

private theorem sixChk4_part3 : (List.range' 57 19).all (sixChk4Row sixAdjL) = true := by
  decide +kernel

private theorem sixChk4_part4 : (List.range' 76 19).all (sixChk4Row sixAdjL) = true := by
  decide +kernel

private theorem sixChk4_part5 : (List.range' 95 16).all (sixChk4Row sixAdjL) = true := by
  decide +kernel

theorem sixChk4_true : sixChk4 = true := by
  have hr : List.range 111 = List.range' 0 19 ++
      (List.range' 19 19 ++
      (List.range' 38 19 ++
      (List.range' 57 19 ++
      (List.range' 76 19 ++
      (List.range' 95 16))))) := rfl
  rw [sixChk4_eq, sixInvAdj_eq, sixChk4G_eq, hr]
  simp only [List.all_append, sixChk4_part0, sixChk4_part1, sixChk4_part2, sixChk4_part3, sixChk4_part4, sixChk4_part5, Bool.and_self]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
