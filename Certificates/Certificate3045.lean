module

public import CFSG.Monster.B.Dyadic.PairK
import Certificates.Kernel.BabyMonster.Pair.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate3045 : CFSG.Monster.B.Dyadic.FactPair :=
  KernelBM.Pair.factPair_of

end Certificates
