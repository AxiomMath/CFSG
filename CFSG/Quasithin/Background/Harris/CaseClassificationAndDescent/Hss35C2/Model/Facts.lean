module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Coord

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model

open CFSG.Quasithin CFSG.Quasithin.F53Mod Equiv
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2 (f5W)

instance instAddCommGroupDual5 : AddCommGroup (Vec →ₗ[ZMod 2] ZMod 2) :=
  letI : AddCommGroup (ZMod 2) := Ring.toAddCommGroup
  LinearMap.addCommGroup

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model
