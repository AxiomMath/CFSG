module

public import CFSG.Certificates.Kernel.FixBoundK.BasicsGlue
public import Certificates.Kernel.FixBoundK.RepFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate812201 : CFSG.Monster.VisQuot.FixBound :=
  KernelFixBoundK.RepFacts.fixBound CFSG.KC.FixBoundK.basicsSem

end Certificates
