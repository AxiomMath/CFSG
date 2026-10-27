module

public import CFSG.RankThree.PartOne.K133B.OddPair
public import CFSG.RankThree.PartOne.K133B.NC5

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.K1320X CFSG.RankThree.PartOne.PAIR22 CFSG.RankThree.PartOne.Q1327T
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def Row8OddHeavy4 : Prop :=
  Row8OddAt (K133.leaf4 0) ∧ Row8OddAt (K133.leaf7 5) ∧ Row8OddAt (K133.leaf7 8) ∧
    Row8OddAt (K133.leaf7 9)

section Four

theorem row8OddHeavy_of_four (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection) (h : Row8OddHeavy4) :
    Row8OddHeavy :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, row8NotCentral5_holds hGA hSLB hInsp⟩

end Four

section Heavy4

theorem kf1322Odd_of_heavy4 (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (h133 : KF133Two)
    (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection) (hHeavy : Row8OddHeavy4) :
    N1322.KF1322Odd :=
  kf1322Odd_of_heavy hGA hS hRe h133 hSLB hInsp (row8OddHeavy_of_four hGA hSLB hInsp hHeavy)

end Heavy4

end CFSG.RankThree.PartOne.K133B
