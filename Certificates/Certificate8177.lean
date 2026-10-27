module

public import Certificates.Data.R3E417.L43

public section

namespace CertificateChecks.Batch8177

open CFSG.RankThree.PartTwo.Sec4.Item434RemL43 CFSG.RankThree.PartTwo.Sec4.Res423Three

set_option maxRecDepth 100000 in
private theorem uniMat_mul_zMat_0 : ∀ a b c d e f : ZMod 3,
    uniMat a b c d e f * zMat = zMat * uniMat a b c d e f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem wMat_comm_1 : ∀ a b c d e f : ZMod 3, ¬ (a = 0 ∧ f = 0) →
    wMat a f * uniMat a b c d e f = uniMat a b c d e f * wMat a f := by
  decide +kernel

private theorem wMat_facts_2 : ∀ a f : ZMod 3, IsR (wMat a f) ∧ (wMat a f).det = 1 ∧
    wMat a f ≠ 1 ∧ wMat a f ≠ zMat ∧ wMat a f ≠ zMat * zMat := by
  decide

end CertificateChecks.Batch8177

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434RemL43 CFSG.RankThree.PartTwo.Sec4.Res423Three in
theorem certificate8177 : (∀ a b c d e f : ZMod 3, uniMat a b c d e f * zMat = zMat * uniMat a b c d e f) ∧
    (∀ a b c d e f : ZMod 3, ¬ (a = 0 ∧ f = 0) →
      wMat a f * uniMat a b c d e f = uniMat a b c d e f * wMat a f) ∧
    (∀ a f : ZMod 3, IsR (wMat a f) ∧ (wMat a f).det = 1 ∧ wMat a f ≠ 1 ∧
      wMat a f ≠ zMat ∧ wMat a f ≠ zMat * zMat) := by
  exact ⟨CertificateChecks.Batch8177.uniMat_mul_zMat_0, CertificateChecks.Batch8177.wMat_comm_1, CertificateChecks.Batch8177.wMat_facts_2⟩

end Certificates
