module

public import CFSG.Monster.B.Classical.E6AdjointTable

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint

namespace CertificateChecks.Batch1954

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint

private theorem invRows_0_0 : invRows 0 13 = true := by
  decide +kernel

private theorem invRows_13_1 : invRows 13 13 = true := by
  decide +kernel

private theorem invRows_26_2 : invRows 26 13 = true := by
  decide +kernel

private theorem invRows_39_3 : invRows 39 13 = true := by
  decide +kernel

private theorem invRows_52_4 : invRows 52 13 = true := by
  decide +kernel

private theorem invRows_65_5 : invRows 65 13 = true := by
  decide +kernel

private theorem genRows_6_6 : genRows 6 = true := by
  decide +kernel

private theorem genRows_7_7 : genRows 7 = true := by
  decide +kernel

private theorem genRows_8_8 : genRows 8 = true := by
  decide +kernel

private theorem genRows_9_9 : genRows 9 = true := by
  decide +kernel

private theorem genRows_10_10 : genRows 10 = true := by
  decide +kernel

private theorem genRows_11_11 : genRows 11 = true := by
  decide +kernel

private theorem genRows_12_12 : genRows 12 = true := by
  decide +kernel

private theorem genRows_14_13 : genRows 14 = true := by
  decide +kernel

private theorem genRows_16_14 : genRows 16 = true := by
  decide +kernel

private theorem genRows_18_15 : genRows 18 = true := by
  decide +kernel

private theorem genRows_20_16 : genRows 20 = true := by
  decide +kernel

private theorem genRows_22_17 : genRows 22 = true := by
  decide +kernel

end CertificateChecks.Batch1954

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint in
theorem certificate1954 : (invRows 0 13 = true)
    ∧ (invRows 13 13 = true)
    ∧ (invRows 26 13 = true)
    ∧ (invRows 39 13 = true)
    ∧ (invRows 52 13 = true)
    ∧ (invRows 65 13 = true)
    ∧ (genRows 6 = true)
    ∧ (genRows 7 = true)
    ∧ (genRows 8 = true)
    ∧ (genRows 9 = true)
    ∧ (genRows 10 = true)
    ∧ (genRows 11 = true)
    ∧ (genRows 12 = true)
    ∧ (genRows 14 = true)
    ∧ (genRows 16 = true)
    ∧ (genRows 18 = true)
    ∧ (genRows 20 = true)
    ∧ (genRows 22 = true) := by
  exact ⟨CertificateChecks.Batch1954.invRows_0_0, CertificateChecks.Batch1954.invRows_13_1, CertificateChecks.Batch1954.invRows_26_2, CertificateChecks.Batch1954.invRows_39_3, CertificateChecks.Batch1954.invRows_52_4, CertificateChecks.Batch1954.invRows_65_5, CertificateChecks.Batch1954.genRows_6_6, CertificateChecks.Batch1954.genRows_7_7, CertificateChecks.Batch1954.genRows_8_8, CertificateChecks.Batch1954.genRows_9_9, CertificateChecks.Batch1954.genRows_10_10, CertificateChecks.Batch1954.genRows_11_11, CertificateChecks.Batch1954.genRows_12_12, CertificateChecks.Batch1954.genRows_14_13, CertificateChecks.Batch1954.genRows_16_14, CertificateChecks.Batch1954.genRows_18_15, CertificateChecks.Batch1954.genRows_20_16, CertificateChecks.Batch1954.genRows_22_17⟩

end Certificates
