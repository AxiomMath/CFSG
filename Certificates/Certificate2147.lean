module

public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.SporSch.Co1.Split

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.Co1Split in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2147 : (Native.splitCheck = true)
    ∧ (Native.splitDataCheck = true)
    ∧ (Native.splitConjCheck = true)
    ∧ (Native.zqCheck = true) := ⟨split, data, conj, zqc⟩

end Certificates
