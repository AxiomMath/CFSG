
module

public import Certificates.Certificate2145Base

public import CFSG.Sporadic.Schreier.Co1RigidCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1LocalExtData
public meta import CFSG.Sporadic.Schreier.Co1RigidCert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.SporSch.Co1.Rigid

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.Co1Rigid in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2145 : (Native.rigCheck = true)
    ∧ (Native.propCheck = true)
    ∧ (Native.freeCheck = true)
    ∧ (Native.basisCheck = true)
    ∧ (∀ ε : Fin 8 → Bool, Native.candOK ε = true) := ⟨rig, prop, free, basis, cand⟩

end Certificates
