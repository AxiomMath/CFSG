module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16
import Certificates.Kernel.Q16Om8.Glue
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace Certificates

open CertificateChecks

theorem certificate320204 : CFSG.CGT.PushingUpLit.SolKNA.R4.NoQ16 ↥CFSG.EvenSmallLie.OmegaEight.omegaT :=
  KernelQ16Om8.q16Om8_noQ16

end Certificates
