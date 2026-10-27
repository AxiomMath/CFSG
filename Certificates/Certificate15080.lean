module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsOct.Glue15080

public section

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru

open scoped Pointwise

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru in
open scoped Pointwise in
theorem certificate15080 :
    titsGen 3 * titsGen 3 = 1 ∧ titsGen 3 0 = 0 ∧ titsGen 1 0 = 0 ∧
    titsGen 1 • titsLine 0 = titsLine 0 ∧ titsGen 2 • titsLine 0 = titsLine 0 ∧
    (∀ v : Fin 2925, 0 ∈ titsLine v →
      v = 0 ∨ ∃ i < 4, (titsGen 1 ^ i * titsGen 3) • titsLine 0 = titsLine v) ∧
    (∀ p : Fin 1755, p ≠ 0 → ∃ b ∈ TA, (b 0 = 0 ∧ b • titsLine 0 = titsLine 0) ∧ b p ≠ p) ∧
    ∀ σ : Equiv.Perm (Fin 1755),
      (∀ p : Fin 1755, octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6 → σ p = p) →
      (∀ b ∈ TA, b 0 = 0 → b • titsLine 0 = titsLine 0 → titsGen 3 * b * titsGen 3 ∈ TA →
        (titsGen 3 * b * titsGen 3) 0 = 0 →
        (titsGen 3 * b * titsGen 3) • titsLine 0 = titsLine 0 → σ * b = b * σ) →
      (titsGen 3 * σ) ^ 2 = 1 → (titsGen 3 * σ * titsGen 2) ^ 35942400 = 1 → σ = 1 :=
  KernelTitsOct.facts15080

end Certificates
