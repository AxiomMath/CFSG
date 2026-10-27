module

public import CFSG.Quasithin.H13.J4Quot
public import CFSG.Quasithin.H13.J4Chain12Spec
public meta import Certificates.Data.CFSGNative.H13.J4Chain12
public meta import Certificates.Data.CFSGNative.H13.J4Data
import Certificates.Data.CFSGNative.H13.J4Data

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Quasithin.H13.J4.Native

@[expose] def uvPairs12 : Array Pr12 :=
  #[(uRows12, uRows12),
    (vRows12, CFSG.Sporadic.SmallF2.Native.mulRows 12 vRows12 vRows12)]

@[expose] def image12Checks : Bool :=
  (CFSG.Sporadic.SmallF2.Native.mulRows 12 uRows12 uRows12 ==
      CFSG.Sporadic.SmallF2.Native.idRows 12) &&
    (CFSG.Sporadic.SmallF2.Native.mulRows 12 vRows12
        (CFSG.Sporadic.SmallF2.Native.mulRows 12 vRows12 vRows12) ==
      CFSG.Sporadic.SmallF2.Native.idRows 12) &&
    witnessOK (mkLevels12 uvPairs12 bases12 words12) &&
    orbitSizes12 (mkLevels12 uvPairs12 bases12 words12) == [693, 2, 30, 4, 8, 2]

end CFSG.Quasithin.H13.J4
