module

public import CFSG.RankThree.PartTwo.Sec19.Ronan1914Leaves316
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofWide3S1919
import CFSG.RankThree.PartTwo.KFacts.KS14GL33
import CFSG.RankThree.PartTwo.Sec19.KS1919G2P
import CFSG.RankThree.PartTwo.Sec19.KS1919U48

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo


theorem item1912_of_item1730_item316
    (h1730 : Sec17.Item1730) (h316 : Item316) :
    Late.Item1912 := by
  have h1914 := Ronan1914.step1914_of_leaves316 h1730 h316
  have h194 := item194UsedWide3_of_item316 h316
  have h1914E := rank3II_19_14E_of h1914 KFacts.ks18M12
  have hsetAt := Sec13.item13SetupAt_of item4_22_holds Sec4.rank3II_4_5
  exact rank3II_19_12_of h1730 Sec13.rank3II_13_1_holds KFacts.KS14.sporadicModels131
    Sec13.slTwoCenter (Late.item13Setup_of hsetAt) hsetAt
    (Sec18.rank3II_18_1_1_of Sec4.item4_44_1_holds) Sec18.item181_2_holds
    (Ronan1914.item195_of_leaves h1730 h316) (Ronan1914.step1918_of_leaves316 h1730 h316)
    (rank3II_19_19_O2_of h1914 h1914E KFacts.KS14.ks18GL33)
    (step1919_of_lie_wide3 Ronan825Y.step1919CoreSplitLie_holds h194 h1914E
      (step1914More_of_step1914 h1914))
    (step1919End_of_parabolic_wide3 h194 h1914 ks1919G2P ks1919U48)

end CFSG.RankThree.PartTwo.Sec19
