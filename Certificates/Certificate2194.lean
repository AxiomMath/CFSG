module

public import CFSG.Sporadic.Schreier.M12PinnedInputs
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M12
import Certificates.Kernel.Mathieu.RootFacts

public section

open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu in
theorem certificate2194 : (MathieuCertificateK "M12" = some m12Record)
    ∧ (m12Record.chain.check 12 = true)
    ∧ (m12Record.chain.orbitSizes 12 = [12, 11, 10, 9, 8])
    ∧ (m12Record.chain.generators = [imageList m12gA, imageList m12gB]) := by
  have h := KernelMathieu.root12
  have e : m12Record = m12RecordK := by rw [m12Record, h.1]; rfl
  rw [← e] at h
  exact h

end Certificates
