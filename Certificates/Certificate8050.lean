module

public import CFSG.Monster.B.Mathieu.SylowSound
import Certificates.Kernel.Mathieu.RootFacts
import Certificates.Kernel.Mathieu.M11Syl
public import CFSG.Sporadic.Schreier.M11PinnedInputs

public section

open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Mathieu in
theorem certificate8050 : (∀ s ∈ m11Record.sylows,
      SylowFacts CFSG.Blueprint.NativeSporadic.M11 7920 [m11gA, m11gB] s)
    ∧ (m11Record.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
      [(2, 5), (3, 4), (5, 1), (11, 1)]) := by
  have e : m11Record = m11RecordK := by rw [m11Record, KernelMathieu.root11.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact KernelMathieu.syl11
  · rw [e]
    decide +kernel

end Certificates
