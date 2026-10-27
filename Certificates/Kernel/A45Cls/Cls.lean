module

public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.A45Cls.Data
meta import Certificates.Kernel.A45Cls.Data

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#conj_orb CertificateChecks.KernelA45.KA CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 45 roots CertificateChecks.KernelA45.rA gens 3

#conj_orb CertificateChecks.KernelA45.KB CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 90 roots CertificateChecks.KernelA45.rB gens 3

#conj_orb CertificateChecks.KernelA45.K36 CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 36 roots CertificateChecks.KernelA45.r36 gens 3

#conj_orb CertificateChecks.KernelA45.K540 CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 108 roots CertificateChecks.KernelA45.r540 gens 3
