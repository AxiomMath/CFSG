module

public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
import Certificates.Kernel.Co1B.C2044

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative in
theorem certificate2044 : (Native.centCheckOf iotaARows twoAD1 twoABray twoAD2 twoAVBase
      twoAVGens twoAVSizes = true
    )
    ∧ (Native.qCheckOf iotaARows twoAD1 twoABray twoAD2 twoAQRows 512 twoARoots
      twoACGens twoACSizes = true
    )
    ∧ (twoAMiscOf iotaARows twoAQRows = true) := KernelCo1B.C2044.c2044

end Certificates
