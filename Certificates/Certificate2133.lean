module

public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
import Certificates.Kernel.SporSch.Co1.Elem
import Certificates.Kernel.SporSch.Co1.ElemE

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2133 : (Native.elemCheck = true)
    ∧ (Native.eCheck = true)
    ∧ (Native.eigenCheck = true) :=
  ⟨KernelSporSch.Co1Elem.elem, KernelSporSch.Co1Elem.e, KernelSporSch.Co1Elem.eigen⟩

end Certificates
