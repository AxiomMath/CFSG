module

public import Certificates.Data.GH74.BTFinCkM23
public meta import Certificates.Data.GH74.BTFinCkM23
import Certificates.Kernel.SporSch.Mathieu.M23FourFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate55103 : Certificates.BTFinCk.M23.m23FourCk = true :=
  KernelSporSch.M23FourK.fourCk

end Certificates
