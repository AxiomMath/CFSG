module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUFacts
import Certificates.Kernel.EvenSporHS.SqprodTwin

public section

open CFSG.EvenSporadicStandard.TwoHS Matrix

set_option maxHeartbeats 0

namespace CertificateChecks.Batch26820

theorem fcard : fVecs.length = 8 ∧ fVecs.Nodup := by decide +kernel

theorem tnot : tVec ∉ fVecs := by decide +kernel

theorem uniq : ∀ v : V4, v + v ∈ fVecs →
    (∀ A ∈ q0List, (A *ᵥ v - v) + (A *ᵥ v - v) = 0) → v + v = 0 := by decide +kernel

theorem comm : ∃ A ∈ q0List, ∀ v : V4, v + v ∈ fVecs →
    (∃ w : V4, v = w - A *ᵥ w) ∨ (∃ w : V4, v - tVec = w - A *ᵥ w) := by decide +kernel

private theorem sqprod : uSqprodCheck = true := by
  rw [EvenSporHS.uSqprodCheck_eq_twin]
  decide +kernel

end CertificateChecks.Batch26820

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26820 : UFactsQ :=
  { fcard := CertificateChecks.Batch26820.fcard, tnot := CertificateChecks.Batch26820.tnot, uniq := CertificateChecks.Batch26820.uniq,
    comm := CertificateChecks.Batch26820.comm, sqprod := sqprod_of_check CertificateChecks.Batch26820.sqprod }

end Certificates
