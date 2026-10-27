module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Kernel.A45Cls.Data3
meta import Certificates.Kernel.A45Cls.Data3

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#left_orb CertificateChecks.KernelA45.TZ CertificateChecks.KernelA45.t0Gen 45 6
  CertificateChecks.KernelA45.ps 64

#left_orb CertificateChecks.KernelA45.QZ CertificateChecks.KernelA45.qGen 45 6
  CertificateChecks.KernelA45.ps 32

#left_orb CertificateChecks.KernelA45.BZ0 CertificateChecks.KernelA45.b2Gen0 45 6
  CertificateChecks.KernelA45.ps 16

#left_orb CertificateChecks.KernelA45.BZ1 CertificateChecks.KernelA45.b2Gen1 45 6
  CertificateChecks.KernelA45.ps 16

#left_orb CertificateChecks.KernelA45.BZ2 CertificateChecks.KernelA45.b2Gen2 45 6
  CertificateChecks.KernelA45.ps 16
