module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinal
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagCoverU43
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagE81
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34PSU3Even
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddFinal
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualFinal
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSL)

section Leaves


theorem item4_44_3Diag_of_leaves
    (h434 : Item4_34Sec)
    (hRS : ∀ m : ℕ, 2 ≤ m → ResidualAt (projSL 3 (GaloisField 2 (2 * m))))
    (hRM : ResidualAt Blueprint.NativeSporadic.M22) : Item4_44_3Diag :=
  item4_44_3Diag_of_inputs
    { kpSz := CFSG.RankThree.PartTwo.KFacts.kpSz
      schreier := CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
      item45 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
      item434Sec := h434
      item41LargePrime := CFSG.RankThree.PartTwo.Sec4.diag_item41LargePrime_holds
      item43 := CFSG.RankThree.PartTwo.Sec4.diag_item43_holds
      coverCenterThree := CFSG.RankThree.PartTwo.Sec4.diag_coverCenterThree_holds
      coverU43Elem := CFSG.RankThree.PartTwo.Sec4.coverU43CenterElem_holds
      e81U43 := CFSG.RankThree.PartTwo.Sec4.e81U43_holds
      e81McL := CFSG.RankThree.PartTwo.Sec4.e81McL_holds
      e81ON := CFSG.RankThree.PartTwo.Sec4.e81ON_holds
      l34PSL3Odd := CFSG.RankThree.PartTwo.Sec4.l34SectionPSL3Odd_holds
      l34PSU3Odd := CFSG.RankThree.PartTwo.Sec4.l34SectionPSU3Odd_holds
      l34PSU3Even := CFSG.RankThree.PartTwo.Sec4.l34SectionPSU3Even_holds
      residualL34 := CFSG.RankThree.PartTwo.Sec4.residualAt_L34_of
        CFSG.RankThree.PartTwo.Sec4.rank3II_4_52_residual
      centerL34 := CFSG.RankThree.PartTwo.Sec4.centerThreePrimeTwoAt_L34_of
        CFSG.RankThree.PartTwo.KFacts.l34CenterThreePrimeTwo
      residualSL3 := hRS
      centerSL3 := CFSG.RankThree.PartTwo.Sec4.diag_centerSL3_holds
      residualM22 := hRM
      centerM22 := CFSG.RankThree.PartTwo.Sec4.diag_centerM22_holds }

theorem item4_44_3Diag_of_item434Sec
    (h434 : Item4_34Sec) : Item4_44_3Diag :=
  item4_44_3Diag_of_leaves h434 residualSL3 residualM22

end Leaves

end CFSG.RankThree.PartTwo.Sec4
