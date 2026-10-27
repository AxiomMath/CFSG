module

public import Certificates.Kernel.MaxD2.HSW0.Glue

public section

namespace Certificates

theorem certificate19843 : Certificates.OverD2Perm.checkW0 Certificates.MaxD2Heis.hsFiveDataP
    Certificates.MaxD2Heis.hsFiveDataR Certificates.HSOver.hsOverW0W Certificates.HSOver.hsOverGAW
    Certificates.HSOver.hsOverGBW = true :=
  CertificateChecks.KernelMaxD2.HSW0.hs_w0

end Certificates
