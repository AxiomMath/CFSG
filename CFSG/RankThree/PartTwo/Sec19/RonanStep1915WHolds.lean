module

public import CFSG.RankThree.PartTwo.Sec19.RonanCensus1915Rows
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec19.RonanSeitz199Holds
public import CFSG.RankThree.PartTwo.Sec4.Item48Proof
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Steps

theorem step1915W_of_step1913
    (h1913 : Step1913) : Step1915W :=
  step1915W_of h1913 Sec4.rank3II_4_5 (Sec4.rank3II_4_8_of Sec4.rank3II_4_5)
      (census1915_of_rowsS Sec4.RonanK429.k429RowsS_holds
          (Sec4.Item41Narrow.item4_1LargePrime_of_griess
              CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
          (PartOne.Mult.exceptionalCenterSmallPrimes_of_griess
              CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement))

theorem step1918_of_step1913_step1917
    (h1913 : Step1913) (h1917 : Step1917) : Step1918 :=
  RonanSeitz199.step1918_of_steps h1913 (step1915W_of_step1913 h1913) h1917

end Steps

end CFSG.RankThree.PartTwo.Sec19
