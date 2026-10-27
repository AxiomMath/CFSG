module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem coreIn_right_le_pCoreOf_left :
    coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ≤ pCoreOf 2 A :=
  (coreIn_le_right _ _).trans inf_le_left

end GoldAmL3

end F6

end CFSG.Quasithin
