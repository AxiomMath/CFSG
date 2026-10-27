module

public import CFSG.Monster.B.Mathieu.SylowSound
import Certificates.Kernel.Mathieu.RootFacts
import Certificates.Kernel.Mathieu.M23Syl
public import CFSG.Sporadic.Schreier.M23PinnedInputs

public section

open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier in
theorem certificate8051 : (∀ s ∈ m23Record.sylows,
      SylowFacts CFSG.Blueprint.NativeSporadic.M23 10200960 [m23PermA, m23PermB] s)
    ∧ (m23Record.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
      [(2, 35), (3, 4), (5, 1), (7, 1), (11, 1), (23, 1)]) := by
  have e : m23Record = m23RecordK := by rw [m23Record, KernelMathieu.root23.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact KernelMathieu.syl23
  · rw [e]
    decide +kernel

end Certificates
