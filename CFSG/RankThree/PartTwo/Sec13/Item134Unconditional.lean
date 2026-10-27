module

public import CFSG.RankThree.PartTwo.Sec13.G131Holds
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.KFacts.KS14Models131
public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailAssembly
public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
public import CFSG.RankThree.PartTwo.Sec4.Item41ScopeProofAll
public import CFSG.RankThree.PartTwo.Sec13.Item133Final
public import CFSG.RankThree.PartTwo.Sec13.KF135Holds
public import CFSG.RankThree.PartTwo.Sec13.K135GL12Mult
public import CFSG.RankThree.PartTwo.Sec13.K135GL12ThmC
public import CFSG.RankThree.PartTwo.Sec13.Item13ResProofReduceAll
import CFSG.RankThree.PartTwo.Sec4.Item422Holds
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

theorem item134_holds
    : Item134 := by
  have h131 : Item131 := Sec13.rank3II_13_1_holds
  have h45 : Sec4.Item4_5 := Sec4.rank3II_4_5
  have h46 : Sec4.Item4_6 := Sec11.Close.closed_sec4Item4_6
  have h47 : Sec4.Item4_7W := Sec11.Close.closed_sec4Item4_7W
  have h48 : Sec4.Item4_8 := Sec11.Close.closed_sec4Item4_8
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have h422 : Sec4.Item4_22 := CFSG.RankThree.PartTwo.item4_22_holds
  have h128 : Sec12.Item128BarAt :=
    Sec12.item128BarAt_of_inputs (Sec11.item1134E27N_of Sec11.Close.narrow_sec9Hyp91SmallNever)
  exact rank3II_13_4_of_steps
      (Sec4.Item426.rank3II_4_26_A6_of h46 h47 KFacts.K426.mclThreeCentralizer
          KFacts.K426.j3CoverCentralizer) Sec4.Sporadic.rank3II_4_15
      (Sec13.item134ON_of h131 h45 h422)
      (item134Arg128_of_item128BarAt h128 h45 h131 KFacts.KS14.sporadicModels131 h415
          Sec4.Sporadic.rank3II_4_14_local h422 h48 CFSG.Sporadic.J2.isSimpleGroup_J2)
      (item134Sylow_of h45 h131 sporadicModels131 Sec4.Sporadic.rank3II_4_15
          (item134SylowBar_of h45 h131 sporadicModels131 Sec4.Sporadic.rank3II_4_15))

theorem item135_holds
    : Item135 := by
  have h131 : Item131 := Sec13.rank3II_13_1_holds
  have h45 : Sec4.Item4_5 := Sec4.rank3II_4_5
  have h422 : Sec4.Item4_22 := CFSG.RankThree.PartTwo.item4_22_holds
  have h131a : Item131a := Sec13.rank3II_13_1a_narrow
  have h44 : Sec4.Item4_4 := Sec4.Census.rank3II_4_4_of_griess_noItem41
  have hK : Item135A7Z3HypTK := Sec13.item135A7Z3HypTK_holds
  have hA7Z3 : Item135A7Z3HypT := Sec13.item135A7Z3HypT_of_K (h131 := h131) (hK := hK)
  have h133 : Item133 := Sec13.rank3II_13_3_of (h131 := h131) (h422 := h422) (h45 := h45)
  have h12 : Item135A7OneTwoCrit2 := F135Last.item135A7OneTwoCrit2_of_gl12
      K135GL12.kFactMultPrimeGL12_holds K135GL12.kFactOutGL12_holds K135GL12.kF135GL12_holds
  have hA7 : Item135A7 := Sec13.item135A7_of_two (h131 := h131) (h133 := h133) (h := h12)
  exact Sec13.rank3II_13_5_of_131a (h131a := h131a) (h44 := h44) (hA7Z3 := hA7Z3) (hA7 := hA7)

end CFSG.RankThree.PartTwo
