
module


public import Certificates.Data.CFSGNative.Bridge.ONGPL
import Certificates.Kernel.Sporadic.ON2.Final
public import Certificates.Certificate9127

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Perm.Native CFSG.Sporadic.Bridge.ONGPL.Native TauCeti in
theorem certificate9217 : bridgeCheck () = true := KernelSpor.ON2.bridge_ok'

end Certificates
