module

public import CFSG.Sporadic.Fi24.OctadsInputs
import Certificates.Kernel.Fi24.OctFacts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Fi24.Native CFSG.Perm CFSG.Perm.Native CFSG.Fischer in
theorem certificate7023 :
    (∀ k, (octF k).card = 8) ∧
      (∀ k k', k ≠ k' → (octF k ∩ octF k').card ≤ 4) ∧
      (∀ k : Fin 759, k.val ≠ 0 →
        (octParF k).val < k.val ∧ octF k = (octF (octParF k)).image (permF (octLabF k))) ∧
      octF 0 = (Finset.univ.filter fun i => permF 0 i = i) ∧
      octF 0 = (octO0.map toFin24).toFinset := KernelFi24.Oct.facts7023

end Certificates
