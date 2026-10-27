module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
import Certificates.Kernel.J2Cover.K4151G

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Sporadic.Schreier.Native in
open CFSG.ComponentClassification.J2Cover (autStrong autBase chainTables) in
open CFSG.ComponentClassification.J2Cover.External (tblX tblY) in
theorem certificate4151 : (countProducts 315 (CFSG.Sporadic.Schreier.Native.commAll 315 [tblX, tblY]) (chainTables 315 autStrong CFSG.ComponentClassification.J2Cover.autBase) (CFSG.Sporadic.Th.Native.idT 315) =
            1) := J2Cover4151.centPD

end Certificates
