module

public import CFSG.Milestones.ASVolI.F431.RonanOddU4
public import CFSG.LargeExtraspecial.AS62C36Main

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF

section Main

theorem lieOfAutCtx : LieOfAutCtx := fun _ _ _ _ _ _ c =>
  CFSG.Quasithin.H13.F431.U42Aut.lieModel_of_autCtx c

theorem oddIndex_U4 : OddIndexU4 :=
  oddIndex_U4_of_lie lieOfAutCtx

end Main

end CFSG.ASVolI
