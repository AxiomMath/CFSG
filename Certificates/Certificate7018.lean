
module

public import Certificates.Certificate7018Base

public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
import Certificates.Kernel.J4F2.H13

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native in
theorem certificate7018 :
    (CFSG.Sporadic.J4.Native.matChecks = true)
    ∧ (tChecks = true) := KernelJ4F2.c7018

end Certificates
