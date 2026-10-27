module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Final
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S9Full

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

theorem b7I2aOddInput_holds : B7I2aOddInput.{u} := by
  intro D _ _ A B z V h hA hb hodd hU
  exact h.I2aProp_of_odd hU (h.I1_of_noACentral hA hU) (h.swapProp_of_noACentral hA) rfl hb hodd

theorem b7CardInput_holds : B7CardInput.{u} :=
  b7CardInput_of_odd b7I2aOddInput_holds

theorem b3FourLeCardInput_holds : B3FourLeCardInput.{u} :=
  b3FourLeCardInput_of_five_seven (b5CardInput_of_b5LeNoAC b5LeNoACInput) b7CardInput_holds

end GoldAmL3

end F6

end CFSG.Quasithin
