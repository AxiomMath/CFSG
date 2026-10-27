module

public import CFSG.YGroups.Y443.Native.BrayWords
public import Certificates.Certificate10111
public meta import CFSG.YGroups.Y443.Native.BrayWords
public meta import CFSG.YGroups.Y443.Native.Align
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords

public section

namespace CFSG.YGroups.Y443

open CFSG.Monster.AxisCount

theorem bray_k_check :
    wordLin (omegaWord ++ kWord) = wordLin (eWord ++ omegaWord) :=
  Certificates.certificate10111.1

theorem bray_g_check :
    wordLin gWord = wordLin (xWord ++ kWord ++ xWord ++ kWord) :=
  Certificates.certificate10111.2.1

theorem bray_comm_check :
    wordLin (xWord ++ gWord) = wordLin (gWord ++ xWord) :=
  Certificates.certificate10111.2.2.1

theorem bray_ne_check :
    wordLin (tWord ++ gWord) ≠ wordLin (gWord ++ tWord) ∧
      wordLin (tWord ++ gWord) ≠ wordLin (gWord ++ tWord ++ xWord) :=
  Certificates.certificate10111.2.2.2

end CFSG.YGroups.Y443
