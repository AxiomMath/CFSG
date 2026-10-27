module

public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Kernel.A45Cls.Data2
meta import Certificates.Kernel.A45Cls.Data2

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#conj_orb CertificateChecks.KernelA45.YB CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 80 roots CertificateChecks.KernelA45.yB gens 3

#conj_orb CertificateChecks.KernelA45.YC CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 96 roots CertificateChecks.KernelA45.yC gens 3

#left_orb CertificateChecks.KernelA45.CB CertificateChecks.KernelA45.cbGen 45 6
  CertificateChecks.KernelA45.ps 72

#left_orb CertificateChecks.KernelA45.CC CertificateChecks.KernelA45.ccGen 45 6
  CertificateChecks.KernelA45.ps 54
