module

public import CFSG.YGroups.Y443.Native.Align
public import Certificates.Certificate10108
public meta import CFSG.YGroups.Y443.Native.Align
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords

public section

namespace CFSG.YGroups.Y443

open CFSG.Monster.AxisCount

theorem align_b :
    wordLin (wcWord ++ omegaWord) = wordLin (omegaWord ++ tWord) :=
  Certificates.certificate10108

end CFSG.YGroups.Y443
