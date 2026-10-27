module

public import CFSG.Sporadic.Co2Schreier.QCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import Certificates.Data.CFSGNative.HS.SmallF2
import Certificates.Kernel.SporSch.Co2M.QMod

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Sporadic.SmallF2.Native in
theorem certificate2056 : qmodCheck witRec = true := KernelSporSch.Co2M.qmod_check

end Certificates
