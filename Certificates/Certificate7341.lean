module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsOct.GlueLam

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.F45Ru in
theorem certificate7341 : ∀ j : Fin 1755, (octGraph.dist (Sum.inl 0) (Sum.inl j) = 2 ∨
      octGraph.dist (Sum.inl 0) (Sum.inl j) = 4 ∨ octGraph.dist (Sum.inl 0) (Sum.inl j) = 6) →
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard
      ≤ 2 ^ 9 ∧
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard
      = 2 ^ 9 ↔ octGraph.dist (Sum.inl 0) (Sum.inl j) = 2) := KernelTitsOct.q12

end Certificates
