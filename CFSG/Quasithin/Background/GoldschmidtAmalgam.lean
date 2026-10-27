module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamN
public import CFSG.Quasithin.Background.GoldschmidtAmalgamS

public section

universe u

namespace CFSG.Quasithin.F6

theorem goldschmidtS3ListCat_of_charTwoLarge (h : GoldschmidtCharTwoLarge.{u}) :
    GoldschmidtS3ListCat.{u} :=
  goldschmidtS3ListCat_of_split goldschmidtNonCharTwoList_holds goldschmidtCharTwoSmall_holds h

end CFSG.Quasithin.F6
