module

public import Certificates.Data.S3x3GL42
import Certificates.Kernel.Misc.GL4.S3Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate320040 : S3x3GL42.Facts :=
  ⟨KernelMisc.GL4S3.classify, KernelMisc.GL4S3.stdI, KernelMisc.GL4S3.stdII⟩

end Certificates
