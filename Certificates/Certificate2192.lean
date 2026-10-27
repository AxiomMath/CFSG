module

public import CFSG.Sporadic.Schreier.M11PinnedInputs
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M11
import Certificates.Kernel.Mathieu.RootFacts

public section

open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu in
theorem certificate2192 : (MathieuCertificateK "M11" = some m11Record)
    ∧ (m11Record.chain.check 11 = true)
    ∧ (m11Record.chain.orbitSizes 11 = [11, 10, 9, 8])
    ∧ (m11Record.chain.generators = [imageList m11gA, imageList m11gB]) := by
  have h := KernelMathieu.root11
  have e : m11Record = m11RecordK := by rw [m11Record, h.1]; rfl
  rw [← e] at h
  exact h

end Certificates
