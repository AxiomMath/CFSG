module

public import Certificates.Data.OmegaTypesFacts
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.Glue218c

public section

namespace Certificates

open CertificateChecks

theorem certificate442005 : OmegaTypes.Facts :=
  ⟨⟨KernelA45.row_tA.1.1, KernelA45.row_tA.1.2.1, KernelA45.row_tA.1.2.2, KernelA45.row_tA.2⟩,
    ⟨KernelA45.row_tB.1.1, KernelA45.row_tB.1.2.1, KernelA45.row_tB.1.2.2, KernelA45.row_tB.2⟩,
    fun _ _ ha hb hab hc => by
      obtain ⟨h1, h2⟩ := KernelA45.card_cent_mul_of_1152 ha.1 hb.1 ha.2.1 hb.2.1 ha.2.2.1
        hb.2.2.1 ha.2.2.2 hb.2.2.2 hab hc
      exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩,
    KernelA45.fact_d, KernelA45.fact_e, KernelA45.fact_f⟩

end Certificates
