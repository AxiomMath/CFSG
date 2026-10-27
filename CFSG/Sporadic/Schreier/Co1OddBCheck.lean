module

public import CFSG.Sporadic.Schreier.Co1OddACCheck
public import CFSG.Sporadic.Co1.Module.TwoBData
public meta import CFSG.Sporadic.Schreier.Co1OddData
public meta import CFSG.Sporadic.Schreier.Co1OddACCheck
public meta import CFSG.Sporadic.Co1.Module.TwoBData
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.Sporadic.Schreier.Co1OddBCheckInputs
public import Certificates.Certificate2143

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

end Native

theorem odd_b_check :
    Native.oddBCheckOf Native.oddBRegs CFSG.Sporadic.Co1.Module.rowsSB = true :=
  Certificates.certificate2143.1

theorem odd_b_basis :
    (CFSG.Sporadic.Co1.OddNative.isFixedN
        (CFSG.Sporadic.SmallF2.Native.transposeRows 24 Native.oddY) (Data.oddSeeds.getD 0 0) &&
      CFSG.Sporadic.Co1.OddNative.isFixedN
        (CFSG.Sporadic.SmallF2.Native.transposeRows 24 Native.oddY) (Data.oddSeeds.getD 1 0) &&
      CFSG.Sporadic.SmallF2.Native.mulRows 24 (Native.inv Native.oddBT) Native.oddBT ==
        CFSG.Sporadic.SmallF2.Native.idRows 24) = true :=
  Certificates.certificate2143.2.1

theorem odd_b_cand :
    Native.oddCandCheckOf Native.oddX Native.oddY CFSG.Sporadic.Co1.Module.rowsSB Native.oddHsB
      Native.oddBT (Native.inv Native.oddBT)
      (CFSG.Sporadic.Co1.OddNative.fixList
        [CFSG.Sporadic.SmallF2.Native.transposeRows 24 Native.oddY]) = true :=
  Certificates.certificate2143.2.2

end CFSG.Sporadic.Co1Schreier
