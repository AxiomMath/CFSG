module

public import CFSG.Sporadic.Schreier.PairJ2FaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairJ2Cert
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.J2.Certificate
import Certificates.Kernel.SporSch.Pair.J2Faith

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 in
open CFSG.Sporadic.J1.Native Matrix in
theorem certificate2235 : j2FaithfulOK = true := KernelSporSch.PJ2Faith.facts

end Certificates
