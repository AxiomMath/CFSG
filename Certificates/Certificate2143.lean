module

public import CFSG.Sporadic.Schreier.Co1OddBCheckInputs
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
import Certificates.Kernel.Co1OddB.Bridge

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2143 : (Native.oddBCheckOf Native.oddBRegs CFSG.Sporadic.Co1.Module.rowsSB = true)
    ∧ ((CFSG.Sporadic.Co1.OddNative.isFixedN
        (CFSG.Sporadic.SmallF2.Native.transposeRows 24 Native.oddY) (Data.oddSeeds.getD 0 0) &&
      CFSG.Sporadic.Co1.OddNative.isFixedN
        (CFSG.Sporadic.SmallF2.Native.transposeRows 24 Native.oddY) (Data.oddSeeds.getD 1 0) &&
      CFSG.Sporadic.SmallF2.Native.mulRows 24 (Native.inv Native.oddBT) Native.oddBT ==
        CFSG.Sporadic.SmallF2.Native.idRows 24) = true
    )
    ∧ (Native.oddCandCheckOf Native.oddX Native.oddY CFSG.Sporadic.Co1.Module.rowsSB Native.oddHsB
      Native.oddBT (Native.inv Native.oddBT)
      (CFSG.Sporadic.Co1.OddNative.fixList
        [CFSG.Sporadic.SmallF2.Native.transposeRows 24 Native.oddY]) = true
    ) := CertificateChecks.KernelCo1OddB.facts2143

end Certificates
