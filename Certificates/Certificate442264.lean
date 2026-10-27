module

public import Certificates.Data.Asc82FbarData
import Certificates.Kernel.P1L43.FbarAll

public section

namespace Certificates

open CertificateChecks

open Certificates.Asc82Fbar CFSG.ComponentClassification.HarrisLit.P1.L43 in
theorem certificate442264 : fbarCheck 80 100000 l43Sift l43Runs (fbarInner ()) (fbarOuter ()) = true := K442264.fbarCheck_true

end Certificates
