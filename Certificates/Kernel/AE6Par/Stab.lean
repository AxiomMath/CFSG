module

public import Certificates.Data.AE6ParData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAE6Par

open CFSG.ClassicalInvolution.Q3 Certificates.AE6Par

theorem ae6par_gstab : ∀ g ∈ List.range 18,
    stabB AE.affinePlanes (genElt g) = true ∧ stabB planes2 (genElt g) = true := by
  decide +kernel

end CertificateChecks.KernelAE6Par
