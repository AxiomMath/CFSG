module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuWords
public import Certificates.Data.TwoF4F48Check
public import Certificates.Certificate15080

public section

namespace CFSG.Quasithin.H13.TwoF4F48

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

open scoped Pointwise

section Facts

theorem n1_sq : titsGen 3 * titsGen 3 = 1 := Certificates.certificate15080.1

theorem n1_zero : titsGen 3 0 = 0 := Certificates.certificate15080.2.1

theorem t_zero : titsGen 1 0 = 0 := Certificates.certificate15080.2.2.1

theorem t_line : titsGen 1 • titsLine 0 = titsLine 0 := Certificates.certificate15080.2.2.2.1

theorem q_line : titsGen 2 • titsLine 0 = titsLine 0 := Certificates.certificate15080.2.2.2.2.1

theorem lines_spec : ∀ v : Fin 2925, 0 ∈ titsLine v →
    v = 0 ∨ ∃ i < 4, (titsGen 1 ^ i * titsGen 3) • titsLine 0 = titsLine v :=
  Certificates.certificate15080.2.2.2.2.2.1

theorem fix_spec : ∀ p : Fin 1755, p ≠ 0 →
    ∃ b ∈ TA, (b 0 = 0 ∧ b • titsLine 0 = titsLine 0) ∧ b p ≠ p :=
  Certificates.certificate15080.2.2.2.2.2.2.1

theorem rigid_spec (σ : Equiv.Perm (Fin 1755))
    (hnear : ∀ p : Fin 1755, octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6 → σ p = p)
    (hcomm : ∀ b ∈ TA, b 0 = 0 → b • titsLine 0 = titsLine 0 → titsGen 3 * b * titsGen 3 ∈ TA →
      (titsGen 3 * b * titsGen 3) 0 = 0 →
      (titsGen 3 * b * titsGen 3) • titsLine 0 = titsLine 0 → σ * b = b * σ)
    (h2 : (titsGen 3 * σ) ^ 2 = 1) (hq : (titsGen 3 * σ * titsGen 2) ^ 35942400 = 1) : σ = 1 :=
  Certificates.certificate15080.2.2.2.2.2.2.2 σ hnear hcomm h2 hq

end Facts

end CFSG.Quasithin.H13.TwoF4F48
