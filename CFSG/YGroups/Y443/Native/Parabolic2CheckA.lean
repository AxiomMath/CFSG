module

public import CFSG.YGroups.Y443.Native.Parabolic2Words
public import Certificates.Certificate10120
public meta import CFSG.YGroups.Y443.Native.Align
public meta import CFSG.YGroups.Y443.Native.Parabolic2Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords

public section

namespace CFSG.YGroups.Y443

open CFSG.Monster.AxisCount

theorem p2_a :
    wordLin (rhoWord ++ rhoWord) = 1 ∧
      (∀ s ∈ rhoGens, wordLin (Lw s ++ rhoWord) = wordLin (rhoWord ++ Lw (armSwapL s))) ∧
      wordLin (omegaWord ++ mWord) = wordLin (rhoWord ++ omegaWord) ∧
      wordLin (zmWord ++ qWord) = wordLin (qWord ++ tWord) :=
  Certificates.certificate10120

end CFSG.YGroups.Y443
