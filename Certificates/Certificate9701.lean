module

public import CFSG.Monster.Schur.TripleM12Data
import Certificates.Kernel.Misc.TripleM12

public section

namespace Certificates

open CFSG.Monster.Schur in
theorem certificate9701 : m12Check = true :=
  CertificateChecks.KernelMisc.TripleM12.m12Check_true

end Certificates
