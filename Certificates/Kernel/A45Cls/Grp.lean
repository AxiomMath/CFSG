module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Kernel.A45Cls.Data
meta import Certificates.Kernel.A45Cls.Data

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#left_orb CertificateChecks.KernelA45.SY CertificateChecks.KernelA45.sGen 45 6
  CertificateChecks.KernelA45.ps 64

#left_orb CertificateChecks.KernelA45.CA CertificateChecks.KernelA45.cGen 45 6
  CertificateChecks.KernelA45.ps 128
