module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeKer
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Final
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EMain

public section

universe u

namespace CFSG.Quasithin.F6.GoldAmLarge

theorem goldschmidtCharTwoLarge_of_three_inputs
    (h3 : GoldAmL3K.B3IntersectionInputThree.{u}) (h4 : GoldAmL3K.B3NoFourInput.{u})
    (h5 : GoldAmLab4.B3DoublyMovedNoFiveInput.{u}) : GoldschmidtCharTwoLarge.{u} :=
  goldschmidtCharTwoLarge_of_inputs GoldAmL2D.b2OmegaInput_holds GoldAmL2T.b2Card64Input_holds
    (GoldAmLab4.b3LabelInput_of_noFour_inputs h4 h5)
    (b3ClassInput_of_intersection (GoldAmL3K.b3IntersectionInput_of_inputs h3 h4))

theorem goldschmidtCharTwoLarge_of_noFive_inputs
    (h4 : GoldAmL3K.B3NoFourInput.{u}) (h5 : GoldAmLab4.B3DoublyMovedNoFiveInput.{u}) :
    GoldschmidtCharTwoLarge.{u} :=
  goldschmidtCharTwoLarge_of_three_inputs GoldAmL3E.b3IntersectionInputThree_holds h4 h5

end CFSG.Quasithin.F6.GoldAmLarge
