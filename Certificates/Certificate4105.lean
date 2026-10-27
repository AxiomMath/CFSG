module

import Certificates.Kernel.J2Cover.K4105
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover in
theorem certificate4105 : (classTotal 315
            #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB]
            #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
            (orderTablesOf (idT 315) 5) 4000 5 2 2 5 = 0) := KernelJ2Cover.total4105

end Certificates
