module

public import CFSG.Monster.B.Mathieu.M22CheckInputs
import Certificates.Kernel.Mathieu.RootFacts

public section

open CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu in
theorem certificate3157 : (MathieuCertificateK "M22" = some m22Record)
    ∧ (m22Record.chain.check 22 = true)
    ∧ (m22Record.chain.orbitSizes 22 = [22, 21, 20, 16, 3])
    ∧ (m22Record.chain.generators = [imageList m22gA, imageList m22gB]) := by
  have h := KernelMathieu.root22
  have e : m22Record = m22RecordK := by rw [m22Record, h.1]; rfl
  rw [← e] at h
  exact h

end Certificates
