module

public import CFSG.Sporadic.Schreier.Co1GenCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1RigidCheck
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1LocalExtData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.SporSch.Co1.Gen

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2136 : Native.genCheck = true := KernelSporSch.Co1Gen.check

end Certificates
