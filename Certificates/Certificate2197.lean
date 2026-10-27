module

public import CFSG.Sporadic.Schreier.M23PinnedInputs
import Certificates.Kernel.Mathieu.RootFacts

public section

open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu in
theorem certificate2197 : (MathieuCertificateK "M23" = some m23Record)
    ∧ (m23Record.chain.check 23 = true)
    ∧ (m23Record.chain.orbitSizes 23 = [23, 22, 21, 20, 3, 16])
    ∧ (m23Record.chain.generators = [imageList m23PermA, imageList m23PermB]) := by
  have h := KernelMathieu.root23
  have e : m23Record = m23RecordK := by rw [m23Record, h.1]; rfl
  rw [← e] at h
  exact h

end Certificates
