module

public import Certificates.Data.CFSGNative.Co2Smith.Check
public import CFSG.Sporadic.Co2Smith.CheckInputs
import Certificates.Kernel.Co2SmithS.Smith

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Smith in
theorem certificate10080 :
    (Native.betaOK seedRowsArr = true)
    ∧ (Native.classOK seedRowsArr = true)
    ∧ (Native.elementsOK seedRowsArr = true)
    ∧ (Native.pairOK seedRowsArr = true)
    ∧ (Native.chainOK seedRowsArr = true)
    ∧ (Native.frameOK seedRowsArr = true)
    ∧ (Native.zetaOK seedRowsArr = true)
    ∧ (Native.xFpfOK seedRowsArr = true)
    ∧ (Native.resOK seedRowsArr = true) := KernelCo2SmithS.smith_ok

end Certificates
