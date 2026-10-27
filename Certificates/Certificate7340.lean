module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsOct.GlueLam

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.F45Ru in
theorem certificate7340 : (∀ p : Fin 1755, (octGraph.neighborSet (Sum.inl p)).ncard = 5) ∧
    (∀ v : Fin 2925, (octGraph.neighborSet (Sum.inr v)).ncard = 3) ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 2}.ncard = 10 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 4}.ncard = 80 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 6}.ncard = 640 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 8}.ncard = 1024 := KernelTitsOct.facts7340

end Certificates
