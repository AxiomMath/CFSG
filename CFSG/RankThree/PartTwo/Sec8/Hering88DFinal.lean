module

public import CFSG.RankThree.PartTwo.Sec8.Hering88DCase3
public import CFSG.RankThree.PartTwo.Sec8.Hering88DCase4
public import CFSG.RankThree.PartTwo.Sec8.Hering88DCase1
public import CFSG.RankThree.PartTwo.Sec8.Hering88DLink
public import CFSG.RankThree.PartTwo.Sec8.Hering88CFinal
import CFSG.RankThree.PartTwo.Sec4.HeringK419Sp4
import CFSG.RankThree.PartTwo.Sec4.HeringK419Sp4Out
import CFSG.RankThree.PartTwo.Sec4.HeringK419G2
import CFSG.RankThree.PartTwo.Sec4.HeringK419F4Holds
import CFSG.RankThree.PartTwo.Sec4.HeringK419Tits
import CFSG.RankThree.PartTwo.Sec4.HeringK419U33
public import CFSG.RankThree.PartTwo.Sec8.Hering88CInv

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88D

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem kF88StepDCaseThreeOdd_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hF : KF84Field) : KF88StepDCaseThreeOdd :=
  kF88StepDCaseThreeOdd_of h45 h84 (kF88SwapCent_holds h45 h84) hF
      (Sec4.k419AutThree_of Sec4.k419AutThreeInnerSp4_holds Sec4.k419AutThreeOuterSp4_holds
          Sec4.k419AutThreeInnerG2_holds Sec4.k419AutThreeOuterG2_holds
          Sec4.k419AutThreeInnerF4_holds Sec4.k419AutThreeOuterF4_holds
          Sec4.k419AutThreeInnerTits_holds Sec4.k419AutThreeInnerU33_holds)
    Hering88C.kF89JCentType419_holds Hering88C.inputs47ClassesD4_holds

theorem kF88StepDCaseFourOdd_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hF : KF84Field) : KF88StepDCaseFourOdd :=
  kF88StepDCaseFourOdd_of h45 h84 (kF88SwapCent_holds h45 h84) hF (Sec4.k419AutThree_of
      Sec4.k419AutThreeInnerSp4_holds Sec4.k419AutThreeOuterSp4_holds Sec4.k419AutThreeInnerG2_holds
      Sec4.k419AutThreeOuterG2_holds Sec4.k419AutThreeInnerF4_holds Sec4.k419AutThreeOuterF4_holds
      Sec4.k419AutThreeInnerTits_holds Sec4.k419AutThreeInnerU33_holds)
    Hering88C.kF89JCentType419_holds Hering88C.inputs47ClassesD4_holds

theorem kF88Step_of_case1ShapesD83
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (h83 : Item83) (hF : KF84Field)
    (hA : KF88Case1ThreeA) (h1 : KF88Case1NontrivOne) (hL : KF88LinkCoreD83) : KF88Step :=
  kF88Step_of_partsD83 h83 (kF88SwapCent_holds h45 h84) (kF88SwapInv_holds h45 h84)
    (kF88StepDData83_of_casesOdd
      (kF88StepDCaseOneOdd_of_inner h45 h84 (kF88SwapCent_holds h45 h84) hF
        (Sec4.k419AutThree_of Sec4.k419AutThreeInnerSp4_holds Sec4.k419AutThreeOuterSp4_holds
            Sec4.k419AutThreeInnerG2_holds Sec4.k419AutThreeOuterG2_holds
            Sec4.k419AutThreeInnerF4_holds Sec4.k419AutThreeOuterF4_holds
            Sec4.k419AutThreeInnerTits_holds Sec4.k419AutThreeInnerU33_holds) Hering88C.kF89JCentType419_holds
        (kF88Case1Inner_of_shapes Hering88C.inputs47ClassesD4_holds hF hA h1))
      (Hering88C.kF88StepDCaseTwo_holds h45 h84 hF).odd (kF88StepDCaseThreeOdd_holds h45 h84 hF)
      (kF88StepDCaseFourOdd_holds h45 h84 hF)
      (Hering88C.kF88StepDCaseFive_holds h45 h84 hF).odd) hL hF

end Hering88D

end CFSG.RankThree.PartTwo.Sec8
