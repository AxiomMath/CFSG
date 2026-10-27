module

public import CFSG.Monster.B.Mathieu.SylowSound
import Certificates.Kernel.Mathieu.RootFacts
import Certificates.Kernel.Mathieu.M22Syl
public import CFSG.Monster.B.Mathieu.M22CheckInputs

public section

open CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu in
theorem certificate3158 : (∀ s ∈ m22Record.sylows,
      SylowFacts CFSG.Blueprint.NativeSporadic.M22 443520 [m22gA, m22gB] s)
    ∧ (m22Record.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
       [(2, 35), (3, 4), (5, 1), (7, 1), (11, 1)]) := by
  have e : m22Record = m22RecordK := by rw [m22Record, KernelMathieu.root22.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact KernelMathieu.syl22
  · rw [e]
    decide +kernel

end Certificates
