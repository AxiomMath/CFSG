module

public import CFSG.Sporadic.SuzRecog.LevelTwoCover
public import CFSG.Sporadic.SuzRecog.LevelTwoGroups

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

open CFSG.Sporadic.SuzRecog.LevelTwo

theorem proj_sC :
    ((proj sC : Model.Crho1) : Equiv.Perm (Fin 1782)) = (sX : Equiv.Perm (Fin 1782)) :=
  congrArg Subtype.val projX_sC

theorem proj_cC
    (j : Fin 2) :
    ((proj (cC j) : Model.Crho1) : Equiv.Perm (Fin 1782)) =
      (cX (mixK j) : Equiv.Perm (Fin 1782)) :=
  congrArg Subtype.val (projX_cC j)

theorem proj_c'C
    (j : Fin 2) :
    ((proj (c'C j) : Model.Crho1) : Equiv.Perm (Fin 1782)) =
      (c'X (mixK j) : Equiv.Perm (Fin 1782)) :=
  congrArg Subtype.val (projX_c'C j)

theorem proj_cell
    (j : Fin 2) :
    ((proj ((cC j)⁻¹ * sC * c'C j) : Model.Crho1) : Equiv.Perm (Fin 1782)) =
      (((cX (mixK j))⁻¹ * sX * c'X (mixK j) : xGroup) : Equiv.Perm (Fin 1782)) := by
  rw [coe_proj]
  show ((projX ((cC j)⁻¹ * sC * c'C j) : xGroup) : Equiv.Perm (Fin 1782)) = _
  rw [map_mul, map_mul, map_inv, projX_cC, projX_sC, projX_c'C]

end CFSG.Sporadic.SuzRecog.LevelTwoCover
