module

public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.LgStabilizer
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.RadNormal

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem pCoreOf_stabSub_eq_radV1 (U : Subgroup (PairN 5)) (hU : U ≤ V1n 5) (hr : rk ↥U = 3) :
    pCoreOf 2 (Lg 5 ⊓ stabSub U) = RadV1 5 U := by
  rw [Lg_inf_stabSub_eq_map_stabMat hU,
    pCoreOf_map_of_injective 2 (pairActN 5) pairActN_injective,
    pCoreOf_stabMat_eq_radMat]
  rfl

end CFSG.ASVolI.ChH
