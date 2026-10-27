module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeFinal
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Main

public section

universe u

namespace CFSG.Quasithin.F6.GoldAmLarge

theorem goldschmidtCharTwoLarge_of_critDist_inputs
    (h1 : GoldAmL3.B3FourLeCardInput.{u}) (h5 : GoldAmL3.B5SymInput.{u})
    (h9 : GoldAmL3.B9Input.{u}) : GoldschmidtCharTwoLarge.{u} :=
  goldschmidtCharTwoLarge_of_noFive_inputs (GoldAmL3.b3NoFourInput_of_reduced h1 h5 h9)
      GoldAmLab4.b3DoublyMovedNoFiveInput

end CFSG.Quasithin.F6.GoldAmLarge
