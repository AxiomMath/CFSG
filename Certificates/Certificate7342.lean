module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsOct.GlueLam

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.F45Ru in
theorem certificate7342 : ∀ (x y x' : Fin 1755) (l : Fin 2925), octGraph.dist (Sum.inl 0) (Sum.inl x) = 2 →
    octGraph.dist (Sum.inl 0) (Sum.inl y) = 2 → octGraph.Adj (Sum.inl 0) (Sum.inr l) →
    octGraph.Adj (Sum.inl x) (Sum.inr l) → octGraph.Adj (Sum.inl x') (Sum.inr l) → x' ≠ 0 →
    x' ≠ x →
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl y) (Sum.inl c) ∧ octGraph.dist (Sum.inl y) (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist (Sum.inl x) (Sum.inl c) ∧ octGraph.dist (Sum.inl x) (Sum.inl c) < 8)} ↔
      y = x') := KernelTitsOct.q7

end Certificates
