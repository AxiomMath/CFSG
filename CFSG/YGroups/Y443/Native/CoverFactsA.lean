module

public import CFSG.YGroups.Y443.Native.CoverFactsWords
public import Certificates.Certificate10112
public meta import CFSG.YGroups.Y443.Native.Align
public meta import CFSG.YGroups.Y443.Native.EdgeNoncomm
public meta import CFSG.YGroups.Y443.Native.CoverFactsWords
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

namespace CFSG.YGroups.Y443

open CFSG.Monster.AxisCount

theorem cover_a :
    wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord) = wordLin (omegaWord ++ coverPHat) ∧
      wordLin (powL 3 coverPHat) = 1 ∧
      wordLin (coverQ ++ omegaWord) = wordLin (omegaWord ++ coverQHat) ∧
      wordLin (coverQHat ++ coverPHat ++ coverWy) = wordLin (coverWy ++ tWord) :=
  Certificates.certificate10112

end CFSG.YGroups.Y443
