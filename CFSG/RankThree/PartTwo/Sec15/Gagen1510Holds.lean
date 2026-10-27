module

public import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProofPGL
public import CFSG.RankThree.PartTwo.Sec13.G131Holds
public import CFSG.RankThree.PartTwo.Sec13.Item133Final
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Main

public section

namespace CFSG.RankThree.PartTwo.Sec15

theorem item1510R_holds
    : Item1510R := by
  have h45 : Sec4.Item4_5 := Sec11.Close.closed_sec4Item4_5
  have h422 : Sec4.Item4_22 :=
    KFacts.rank3II_4_22_of_items_noItem41 h45 Sec11.Close.closed_tBLitGriessMultipliersAllModels
      Sec11.Close.closed_sec4Item4_3
  have h131 : Sec13.Item131 := Sec13.rank3II_13_1_holds
  exact item1510R_of_fuse h131 (Sec13.rank3II_13_3_of h131 h422 h45)
    (Sec13.item13SetupAt_of h422 h45) Proof1510Fuse.step1510PGLFuse_holds

end CFSG.RankThree.PartTwo.Sec15
