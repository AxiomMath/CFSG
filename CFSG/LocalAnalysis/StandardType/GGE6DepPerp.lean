module

public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs

public section

namespace CFSG.StandardType

theorem ggCoxeterLabelResidualInput_of_e6DepPerp (hO : GGCoxeterLabelResidualOffE6DepInput)
    (hE : GGE6DepPerpExcl) : GGCoxeterLabelResidualInput := by
  intro G _ _ p B Bs x L D J config opAut innerDiag noTransvection y K neighbour
    reflectionGenerated scalars _ noFork noStandard
  exact hO G p B Bs x L D J config opAut innerDiag noTransvection y K neighbour
    reflectionGenerated scalars noFork noStandard
    (hE G p B Bs x L D J config opAut innerDiag noTransvection y K neighbour)

theorem ggCorFiveTwentyInputQTwo_of_e6DepPerp (hO : GGCorFiveTwentyInputQTwoOffE6Dep)
    (hE : GGE6DepPerpExcl) : GGCorFiveTwentyInputQTwo :=
  fun G _ _ p B Bs x L D J hH hL =>
    hO G p B Bs x L D J hH hL
      (hE G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1)

end CFSG.StandardType
