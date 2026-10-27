module

public import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres
import Certificates.Kernel.Co2SmithS.Seeds
public import CFSG.Sporadic.Co2Smith.CheckInputs

public section

open CFSG.Sporadic.Co2Smith

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Smith in
theorem certificate10085 :
    Native.sp6Check seedRowsArr = true :=
  (CFSG.KC.Co2SmithS.sp6Check_eq KernelCo2SmithS.sp6Letters_get KernelCo2SmithS.mRows_two
    KernelCo2SmithS.mRows_three
    ⟨CFSG.KC.Co2InvS.mulV_lt _ _, CFSG.KC.Co2InvS.mulV_lt _ _⟩).trans KernelCo2SmithS.sp6_ok

end Certificates
