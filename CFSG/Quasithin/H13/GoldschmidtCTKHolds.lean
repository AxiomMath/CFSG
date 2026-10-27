module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamOdd
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwo
public import CFSG.Quasithin.H13.GoldschmidtCTKFamL45
public import CFSG.Quasithin.H13.GoldschmidtCTKFamSpor

public section


namespace CFSG.Quasithin.H13.CTK

theorem exclA5Block_holds : ExclA5Block :=
  exclA5Block_of_families exclA5BlockFor_alt exclA5BlockFor_odd exclA5BlockFor_two
    exclA5BlockFor_l45 exclA5BlockFor_spor

end CFSG.Quasithin.H13.CTK
