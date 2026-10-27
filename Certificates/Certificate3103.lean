module

public import CFSG.Monster.B.Dyadic.Facts
import Certificates.Kernel.BabyMonster.Facts3103

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelBM.Lat

theorem certificate3103 : CFSG.Monster.B.Dyadic.Fact3103 :=
  ⟨stats_text, fixed_bits⟩

end Certificates
