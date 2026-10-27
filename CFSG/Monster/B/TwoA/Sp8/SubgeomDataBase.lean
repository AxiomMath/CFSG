
module

public import CFSG.Monster.B.TwoA.Base.IncidenceBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

attribute [local instance] parAction

theorem smul_obj_snd (s : Shat) (x : ParGeom) :
    (s • x : ParGeom).1.2 = conjSub (s : Dfull) x.1.2 := rfl

end CFSG.Monster.B.TwoA.Sp8
