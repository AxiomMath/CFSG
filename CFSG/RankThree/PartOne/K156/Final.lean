module

public import CFSG.RankThree.PartOne.K156.Five

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.S15K (Sec13Avail)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf156'_of_full106
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (h106 : Full106Stmt)
    (hS13 : Sec13Avail) (h1322 : Node1322) (h1320 : Node1320Struct) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h128 : Node128) : KF156' := by
  intro G _ _ p A c L E h15 hF hout X hX
  rcases hout with ⟨f, -, -, -, -, hEA, -⟩ | ⟨f, -, -, -, -, hEA, -⟩ | ⟨f, -, -, -, -, hEA, -⟩ |
      ⟨f, -, -, -, -, hEA, -⟩ | hout
  · exact kf156_of_E_eq_A hGA hS hTwo h106 hS13 h1322 h1320 h15 hEA X hX
  · exact kf156_of_E_eq_A hGA hS hTwo h106 hS13 h1322 h1320 h15 hEA X hX
  · exact kf156_of_E_eq_A hGA hS hTwo h106 hS13 h1322 h1320 h15 hEA X hX
  · exact kf156_of_E_eq_A hGA hS hTwo h106 hS13 h1322 h1320 h15 hEA X hX
  · exact kf156_of_five hGA hS hTwo h106 h11 h122 h122b h123 h124 h125 h128 h15 hF hout X hX

end CFSG.RankThree.PartOne.K156
