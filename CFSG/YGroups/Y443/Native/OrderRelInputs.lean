module

public import CFSG.YGroups.Y443.Native.Words

@[expose] public section

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

@[expose] def orderWords : List (List Native.Gen) := (List.range 11).map orderWord

end CFSG.YGroups.Y443
