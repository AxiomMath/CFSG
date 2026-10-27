module

public import CFSG.LieType.Chevalley.RootCommutatorPairTable

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch3951

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem closureCheck_E8_0_lo_0 : closureCheck .E8 ⟨0, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_0_hi_1 : closureCheck .E8 ⟨0, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_1_lo_2 : closureCheck .E8 ⟨1, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_1_hi_3 : closureCheck .E8 ⟨1, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_2_lo_4 : closureCheck .E8 ⟨2, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_2_hi_5 : closureCheck .E8 ⟨2, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_3_lo_6 : closureCheck .E8 ⟨3, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_3_hi_7 : closureCheck .E8 ⟨3, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_4_lo_8 : closureCheck .E8 ⟨4, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_4_hi_9 : closureCheck .E8 ⟨4, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_5_lo_10 : closureCheck .E8 ⟨5, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_5_hi_11 : closureCheck .E8 ⟨5, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_6_lo_12 : closureCheck .E8 ⟨6, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_6_hi_13 : closureCheck .E8 ⟨6, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem closureCheck_E8_7_lo_14 : closureCheck .E8 ⟨7, by decide⟩ 0 120 = true := by
  decide +kernel

private theorem closureCheck_E8_7_hi_15 : closureCheck .E8 ⟨7, by decide⟩ 120 240 = true := by
  decide +kernel

private theorem negCheck_E8_16 : negCheck .E8 = true := by
  decide +kernel

private theorem tableCheck_E8_17 : tableCheck .E8 = true := by
  decide +kernel

private theorem sizeCheck_E8_0_18 : sizeCheck .E8 0 = true := by
  decide +kernel

private theorem sizeCheck_E8_1_19 : sizeCheck .E8 1 = true := by
  decide +kernel

private theorem sizeCheck_E8_2_20 : sizeCheck .E8 2 = true := by
  decide +kernel

end CertificateChecks.Batch3951

namespace Certificates

open CertificateChecks

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate3951 : ((closureCheck .E8 ⟨0, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨0, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨1, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨1, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨2, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨2, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨3, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨3, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨4, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨4, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨5, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨5, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨6, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨6, by decide⟩ 120 240 = true)
      ∧ (closureCheck .E8 ⟨7, by decide⟩ 0 120 = true ∧
          closureCheck .E8 ⟨7, by decide⟩ 120 240 = true))
    ∧ negCheck .E8 = true ∧ tableCheck .E8 = true
      ∧ sizeCheck .E8 0 = true ∧ sizeCheck .E8 1 = true ∧ sizeCheck .E8 2 = true := by
  exact ⟨⟨⟨CertificateChecks.Batch3951.closureCheck_E8_0_lo_0, CertificateChecks.Batch3951.closureCheck_E8_0_hi_1⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_1_lo_2, CertificateChecks.Batch3951.closureCheck_E8_1_hi_3⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_2_lo_4, CertificateChecks.Batch3951.closureCheck_E8_2_hi_5⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_3_lo_6, CertificateChecks.Batch3951.closureCheck_E8_3_hi_7⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_4_lo_8, CertificateChecks.Batch3951.closureCheck_E8_4_hi_9⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_5_lo_10, CertificateChecks.Batch3951.closureCheck_E8_5_hi_11⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_6_lo_12, CertificateChecks.Batch3951.closureCheck_E8_6_hi_13⟩,
    ⟨CertificateChecks.Batch3951.closureCheck_E8_7_lo_14, CertificateChecks.Batch3951.closureCheck_E8_7_hi_15⟩⟩,
    CertificateChecks.Batch3951.negCheck_E8_16, CertificateChecks.Batch3951.tableCheck_E8_17, CertificateChecks.Batch3951.sizeCheck_E8_0_18,
    CertificateChecks.Batch3951.sizeCheck_E8_1_19, CertificateChecks.Batch3951.sizeCheck_E8_2_20⟩

end Certificates
