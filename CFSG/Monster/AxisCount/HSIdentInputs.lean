module

public import CFSG.Monster.AxisCount.HSIdentRec0Inputs
public import CFSG.Monster.AxisCount.HSIdentRec1Inputs
public import CFSG.Monster.AxisCount.HSIdentRec2Inputs
public import CFSG.Monster.AxisCount.HSIdentRec3Inputs
public import CFSG.Monster.AxisCount.HSIdentRec4Inputs
public import CFSG.Monster.AxisCount.HSIdentRec5Inputs
public import CFSG.Monster.AxisCount.HSIdentRec6Inputs
public import CFSG.Monster.AxisCount.HSIdentRec7Inputs
public import CFSG.Monster.B.Short.AxisOrbit

public section

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.B.Short

@[expose] def recShards : List (Fin 12 × Nat × Nat) :=
  recShard_0 ++
    recShard_1 ++
    recShard_2 ++
    recShard_3 ++
    recShard_4 ++
    recShard_5 ++
    recShard_6 ++
    recShard_7

end CFSG.Monster.AxisCount.HS
