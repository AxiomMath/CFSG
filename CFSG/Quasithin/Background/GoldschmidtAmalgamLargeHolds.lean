module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeR
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SSym
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Done
public import CFSG.Quasithin.Background.GoldschmidtAmalgam

public section

universe u

namespace CFSG.Quasithin.F6

namespace GoldAmLarge

theorem goldschmidtCharTwoLarge_holds :
    GoldschmidtCharTwoLarge.{u} :=
  goldschmidtCharTwoLarge_of_critDist_inputs GoldAmL3.b3FourLeCardInput_holds GoldAmL3.b5SymInput
      GoldAmL3.b9Input

end GoldAmLarge

theorem goldschmidtS3ListCat_holds :
    GoldschmidtS3ListCat.{u} :=
  goldschmidtS3ListCat_of_charTwoLarge GoldAmLarge.goldschmidtCharTwoLarge_holds

end CFSG.Quasithin.F6
