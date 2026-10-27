module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1F0Check
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
import Certificates.Kernel.Co1B.C129070

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129070 : f0Check () = true := KernelCo1B.C129070.c129070

end Certificates
