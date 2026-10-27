module

public import CFSG.Blueprint.ChevalleyStringsInputs
import Certificates.Certificate113
import Certificates.Kernel.ChevStrChecks
import CFSG.Certificates.Kernel.ChevStrSound

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace CertificateChecks.Batch114

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley


namespace StringData

variable {τ : Tag} (S : StringData τ) (C : RootCertificate τ)

variable {S C}

end StringData

namespace StringData

variable {τ : Tag} {S : StringData τ} {C : RootCertificate τ}

end StringData

private theorem check_of {τ : Tag} {S : StringData τ} {C : RootCertificate τ} {P : ℕ}
    (hb : S.checkBuckets C = true) (hbb : S.checkBucketBounds C = true)
    (hc : CFSG.KC.ChevStr.coordsK τ.rank S.maxCoord C.roots = true)
    (ht : CFSG.KC.ChevStr.top τ.rank P (2 * S.maxCoord + 1) C.roots S.strings = true) :
    S.check C = true := by
  rw [StringData.check, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hb, hbb⟩, CFSG.KC.ChevStr.checkCoords_of_coordsK hc⟩,
    CFSG.KC.ChevStr.checkStrings_of_top P hb hbb ht⟩

open CertificateChecks.ChevStr

private theorem g2StringData_check : g2StringData.check g2Certificate = true :=
  check_of ch114_g2_buckets ch114_g2_bounds ch114_g2_coords ch114_g2_top
private theorem f4StringData_check : f4StringData.check f4Certificate = true :=
  check_of ch114_f4_buckets ch114_f4_bounds ch114_f4_coords ch114_f4_top
private theorem d4StringData_check : d4StringData.check d4Certificate = true :=
  check_of ch114_d4_buckets ch114_d4_bounds ch114_d4_coords ch114_d4_top
private theorem e6StringData_check : e6StringData.check e6Certificate = true :=
  check_of ch114_e6_buckets ch114_e6_bounds ch114_e6_coords ch114_e6_top
private theorem e7StringData_check : e7StringData.check e7Certificate = true :=
  check_of ch114_e7_buckets ch114_e7_bounds ch114_e7_coords ch114_e7_top
private theorem e8StringData_check : e8StringData.check e8Certificate = true :=
  check_of ch114_e8_buckets ch114_e8_bounds ch114_e8_coords ch114_e8_top

end CertificateChecks.Batch114

namespace Certificates

open CertificateChecks

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem certificate114 : (g2StringData.check g2Certificate = true)
    ∧ (f4StringData.check f4Certificate = true)
    ∧ (d4StringData.check d4Certificate = true)
    ∧ (e6StringData.check e6Certificate = true)
    ∧ (e7StringData.check e7Certificate = true)
    ∧ (e8StringData.check e8Certificate = true) := by
  exact ⟨CertificateChecks.Batch114.g2StringData_check, CertificateChecks.Batch114.f4StringData_check, CertificateChecks.Batch114.d4StringData_check, CertificateChecks.Batch114.e6StringData_check, CertificateChecks.Batch114.e7StringData_check, CertificateChecks.Batch114.e8StringData_check⟩

end Certificates
