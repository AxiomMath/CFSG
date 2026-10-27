module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DLarge
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2T
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLarge
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab3Ker
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub3

public section

universe u

namespace CFSG.Quasithin.F6.GoldAmLarge

theorem b3ClassInput_of_intersection
    (hi : GoldAmL3.B3IntersectionInput.{u}) : B3ClassInput.{u} :=
  fun _ _ _ _ _ _ _ h _ =>
    GoldAmL3c.isGoldCaseM12_or_aut_of_inputs (GoldAmL3.b3CardInput_of_intersection hi) hi h

end CFSG.Quasithin.F6.GoldAmLarge
