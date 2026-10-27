module

public import CFSG.Quasithin.H13.U3SixNormInputs

public section

namespace CertificateChecks.Batch16950

private theorem dGL_not_mem_rhoT_0 :
    ∀ e ∈ CFSG.Quasithin.H13.U3.tc, CFSG.Quasithin.H13.U3.canon6 e = true := by
  decide +kernel

end CertificateChecks.Batch16950

namespace Certificates

open CertificateChecks

theorem certificate16950 : ∀ e ∈ CFSG.Quasithin.H13.U3.tc, CFSG.Quasithin.H13.U3.canon6 e = true := by
  exact CertificateChecks.Batch16950.dGL_not_mem_rhoT_0

end Certificates
