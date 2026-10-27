module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SSym
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Done
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeKer
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic

public section

universe u

namespace CFSG.Quasithin

namespace F6

namespace GoldAmLarge

theorem goldschmidtCharTwoLargeV_holds :
    GoldschmidtCharTwoLargeV.{u} :=
  goldschmidtCharTwoLargeV_of_inputs GoldAmL2D.b2OmegaInput_holds GoldAmL2T.b2Card64Input_holds
    (GoldAmLab4.b3LabelInput_of_noFour_inputs
      (GoldAmL3.b3NoFourInput_of_reduced GoldAmL3.b3FourLeCardInput_holds GoldAmL3.b5SymInput
        GoldAmL3.b9Input)
      GoldAmLab4.b3DoublyMovedNoFiveInput)
    (b3ClassInput_of_intersection
      (GoldAmL3K.b3IntersectionInput_of_inputs GoldAmL3E.b3IntersectionInputThree_holds
        (GoldAmL3.b3NoFourInput_of_reduced GoldAmL3.b3FourLeCardInput_holds GoldAmL3.b5SymInput
          GoldAmL3.b9Input)))

theorem goldschmidtCharTwoLargePair_holds :
    GoldschmidtCharTwoLargePair.{u} :=
  goldschmidtCharTwoLargePair_of_v goldschmidtCharTwoLargeV_holds

end GoldAmLarge

end F6

end CFSG.Quasithin
