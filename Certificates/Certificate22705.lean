module

public import Certificates.Data.GrSLitHeF3
import Certificates.Kernel.CF23L34.HeF3Glue

public section

namespace Certificates

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB Certificates.GrSLitHeZStar Certificates.GrSLitHeF3 in
theorem certificate22705 :
    comp 8330 heF3W1Tab heF3W1Tab = idTab 8330 ∧ comp 8330 heF3W2Tab heF3W2Tab = idTab 8330 ∧
      heF3W12Tab = comp 8330 heF3W2Tab heF3W1Tab ∧
      heF3W1Tab ≠ idTab 8330 ∧ heF3W1Tab ≠ heGen 0 ∧ heF3W1Tab ≠ heZUTab ∧
      heF3W1Tab ≠ heZT0UTab ∧
      heF3W2Tab ≠ idTab 8330 ∧ heF3W2Tab ≠ heGen 0 ∧ heF3W2Tab ≠ heZUTab ∧
      heF3W2Tab ≠ heZT0UTab ∧
      heF3W12Tab ≠ idTab 8330 ∧ heF3W12Tab ≠ heGen 0 ∧ heF3W12Tab ≠ heZUTab ∧
      heF3W12Tab ≠ heZT0UTab :=
  CertificateChecks.KernelLC.HeF3.check22705

end Certificates
