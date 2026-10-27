module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLarge

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL2D

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem b2OmegaInput_holds : GoldAmLarge.B2OmegaInput.{u} := by
  intro D _ _ A B z V h h32 hn hb
  exact a1_trivial_of_critDist_two h h32 hn hb

end GoldAmL2D

end F6

end CFSG.Quasithin
