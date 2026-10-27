module

public import CFSG.Monster.B.Mathieu.M24CheckInputs
import Certificates.Kernel.Mathieu.RootFacts

public section

open CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu in
theorem certificate3046 : (MathieuCertificateK "M24" = some m24Record)
    ∧ (m24Record.chain.check 24 = true)
    ∧ (m24Record.chain.orbitSizes 24 = [24, 23, 22, 21, 20, 16, 3])
    ∧ (m24Record.chain.generators = [imageList m24gA, imageList m24gB]) := by
  have h := KernelMathieu.root24
  have e : m24Record = m24RecordK := by rw [m24Record, h.1]; rfl
  rw [← e] at h
  exact h

end Certificates
