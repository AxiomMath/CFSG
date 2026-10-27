module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Sym
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeNoAC

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7 CFSG.Quasithin.F6.GoldAmLab8

namespace F6

namespace GoldAmL3

theorem b5LeNoACInput_of_notNormalBTwoSys
    (hP : ∀ (D : Type u) [Group D] [Finite D], NotNormalBTwoSys D) : B5LeNoACInput.{u} :=
  fun D _ _ _ _ _ _ h hb _ => noACentral_of_notNormalBTwoSys (hP D) h hb

end GoldAmL3

end F6

end CFSG.Quasithin
