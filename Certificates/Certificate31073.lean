module

public import Certificates.Data.ThreeFourTwoHSU35
import Certificates.Kernel.MaxD2.HSU35L.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate31073 : Certificates.ThreeFourTwoHSU35.hsU35Check () = true :=
  KernelMaxD2.HSU35L.check

end Certificates
