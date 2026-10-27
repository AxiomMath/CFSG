module

public import Certificates.Data.FooteLitCF23J2Check
import Certificates.Kernel.Sporadic.OddCore.J2Fus

public section

namespace Certificates

open CFSG.ComponentClassification.GSThmB.CF23I.J2 in
theorem certificate23202 : j2FusOK = true :=
  CertificateChecks.KernelSpor.J2Fus.j2FusOK_of

end Certificates
