module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.M24CatInputs
import Certificates.Kernel.LieOrders.M24

public section

namespace Certificates

open CertificateChecks

theorem certificate25280 : CFSG.EvenSporadicStandard.TwoFi22.DS81.m24LieCheck = true :=
  KernelLieOrders.m24LieCheck_true

end Certificates
