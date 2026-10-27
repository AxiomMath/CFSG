module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofWire
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofTwentySeven
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofHessL
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowPGL
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowInner
public import CFSG.RankThree.PartTwo.Sec13.G131Holds
public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailAssembly
public import CFSG.RankThree.PartTwo.Sec13.Item133Final
public import CFSG.RankThree.PartTwo.Sec6.HeringGWLBalance

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem closedInputs
    :
    Sec4.Item4_5 ∧ Sec4.Item4_8 ∧ Sec4.Item4_1LargePrime ∧ Sec4.Item4_22 ∧ Sec4.Item4_6 ∧
      Sec4.Item4_15 ∧ Sec6.GWLBalanceStatement ∧ Item131 ∧ Item134 ∧ Item133 ∧
      Item142AllS14 := by
  have h45 : Sec4.Item4_5 := Sec11.Close.closed_sec4Item4_5
  have h48 : Sec4.Item4_8 := Sec11.Close.closed_sec4Item4_8
  have h41 : Sec4.Item4_1LargePrime := Sec4.diag_item41LargePrime_holds
  have h422 : Sec4.Item4_22 :=
    KFacts.rank3II_4_22_of_items_noItem41 h45 Sec11.Close.closed_tBLitGriessMultipliersAllModels
      Sec11.Close.closed_sec4Item4_3
  have h46 : Sec4.Item4_6 := Sec11.Close.closed_sec4Item4_6
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hGW : Sec6.GWLBalanceStatement := Sec6.gwlBalanceStatement_holds
  have h131 : Item131 := rank3II_13_1_holds
  have h128 : Sec12.Item128BarAt :=
    Sec12.item128BarAt_of_inputs (Sec11.item1134E27N_of Sec11.Close.narrow_sec9Hyp91SmallNever)
  have h134 : Item134 :=
    rank3II_13_4_of_steps
        (Sec4.Item426.rank3II_4_26_A6_of h46 Sec11.Close.closed_sec4Item4_7W
            KFacts.K426.mclThreeCentralizer KFacts.K426.j3CoverCentralizer)
        Sec4.Sporadic.rank3II_4_15 (item134ON_of h131 h45 h422)
        (item134Arg128_of_item128BarAt h128 h45 h131 Sec13.sporadicModels131 h415
            Sec4.Sporadic.rank3II_4_14_local h422 h48 CFSG.Sporadic.J2.isSimpleGroup_J2)
        (item134Sylow_of h45 h131 sporadicModels131 Sec4.Sporadic.rank3II_4_15
            (item134SylowBar_of h45 h131 sporadicModels131 Sec4.Sporadic.rank3II_4_15))
  have h133 : Item133 := rank3II_13_3_of h131 h422 h45
  have h142 : Item142AllS14 := item142AllS14_of_leaves11 h131 h134 h48 h422 h45
      ks142L3HessGenNineModel_proof step142LowerGenL3PGL_proof step142TypesL3InnerPow_proof
      step142TypesL3PGL_proof
  exact ⟨h45, h48, h41, h422, h46, h415, hGW, h131, h134, h133, h142⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148M
