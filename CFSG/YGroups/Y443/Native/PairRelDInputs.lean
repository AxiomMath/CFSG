module

public import CFSG.YGroups.Y443.Native.Words

@[expose] public section

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

def pairDWords : List (List Native.Gen) := pairWords [5, 6, 7, 8, 9]

end CFSG.YGroups.Y443
