module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUFacts
import Certificates.Kernel.EvenSporHS.SqprodW
import Certificates.Kernel.EvenSporHS.SqprodWData

public section

open CFSG.EvenSporadicStandard.TwoHS Matrix

set_option maxHeartbeats 0

namespace CertificateChecks.Batch26820

theorem fcard : fVecs.length = 8 ∧ fVecs.Nodup := by decide +kernel

theorem tnot : tVec ∉ fVecs := by decide +kernel

def a0 : M4 := matOfList [0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 1, 2, 0, 1, 0, 1]

def bW : M4 := matOfList [2, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 1, 1, 0, 1]

theorem a0mem : a0 ∈ q0List := by decide +kernel

theorem a0fix : ∀ f ∈ fVecs, a0 *ᵥ f = f → f = 0 := by decide +kernel

theorem commW : ∀ v : V4, v + v ∈ fVecs →
    v = bW *ᵥ v - a0 *ᵥ (bW *ᵥ v) ∨ v - tVec = bW *ᵥ v - a0 *ᵥ (bW *ᵥ v) := by decide +kernel

theorem uniq : ∀ v : V4, v + v ∈ fVecs →
    (∀ A ∈ q0List, (A *ᵥ v - v) + (A *ᵥ v - v) = 0) → v + v = 0 := by
  intro v hv h
  refine a0fix _ hv ?_
  rw [← sub_eq_zero, Matrix.mulVec_add, ← sub_add_sub_comm]
  exact h a0 a0mem

theorem comm : ∃ A ∈ q0List, ∀ v : V4, v + v ∈ fVecs →
    (∃ w : V4, v = w - A *ᵥ w) ∨ (∃ w : V4, v - tVec = w - A *ᵥ w) :=
  ⟨a0, a0mem, fun v hv => (commW v hv).imp (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)⟩

private theorem sqq : EvenSporHS.eqL q0R EvenSporHS.q0N = true := by decide +kernel

private theorem squ : EvenSporHS.subL EvenSporHS.uN EvenSporHS.q0N = true := by decide +kernel

private theorem sqw : EvenSporHS.wOK EvenSporHS.uN EvenSporHS.q0N EvenSporHS.wN = true := by
  decide +kernel

end CertificateChecks.Batch26820

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26820 : UFactsQ :=
  { fcard := CertificateChecks.Batch26820.fcard, tnot := CertificateChecks.Batch26820.tnot, uniq := CertificateChecks.Batch26820.uniq,
    comm := CertificateChecks.Batch26820.comm, sqprod := EvenSporHS.sqprod_of_w Batch26820.sqq Batch26820.squ Batch26820.sqw }

end Certificates
