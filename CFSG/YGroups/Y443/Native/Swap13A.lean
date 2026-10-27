module

public import CFSG.YGroups.Y443.Native.Swap13Word
public import Certificates.Certificate10124
public meta import CFSG.YGroups.Y443.Native.Align
public meta import CFSG.YGroups.Y443.Native.Parabolic2Words
public meta import CFSG.YGroups.Y443.Native.Swap13Word
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords

public section

namespace CFSG.YGroups.Y443

open CFSG.Monster.AxisCount

theorem swap13_a :
    wordLin (tWord ++ swap13Word) = wordLin (swap13Word ++ tWord) ∧
      wordLin (mtmWord ++ swap13Word) = wordLin (swap13Word ++ zmWord) :=
  Certificates.certificate10124

end CFSG.YGroups.Y443
