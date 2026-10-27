module

public import CFSG.Certificates.Kernel.BabyMonster.SevenFacts
import Certificates.Kernel.BabyMonster.SevenLocal

public section

namespace Certificates

open CertificateChecks

theorem certificate17450 : CFSG.KC.BM.SevenFacts.Fact17450 :=
  KernelBM.SevenFacts.fact17450

end Certificates
