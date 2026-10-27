module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Defs
import Certificates.Kernel.G23F48.Restate

public section

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7762 : burnsideF48t_g23X = Subgroup.closure (Set.range fun i : Fin 4 => burnsideF48t_g23γ i) ∧
    burnsideF48t_g23P1' =
      Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1, burnsideF48t_g23σ 2} ∧
    burnsideF48t_g23P2' =
      Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1, burnsideF48t_g23σ 3} ∧
    burnsideF48t_g23B' = Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1} ∧
    (∀ i < 4, burnsideF48t_g23σ i ∈ burnsideF48t_g23X) ∧
    (∀ i < 4, burnsideF48t_g23τ * burnsideF48t_g23γ i * burnsideF48t_g23τ⁻¹ ∈ burnsideF48t_g23X) ∧
    burnsideF48t_g23S0' ≤ burnsideF48t_g23B' ∧ burnsideF48t_g23K' ≤ burnsideF48t_g23B' ∧
    (∀ r ∈ burnsideF48t_g23R1 ++ burnsideF48t_g23R2 ++
      [(List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten],
      burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_g23σ i) r = 1) ∧
    (¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 0 =
        burnsideF48t_g23κ 0 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
      ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 1 =
        burnsideF48t_g23κ 1 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
      ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) =
        (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) *
          (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3))) ∧
    364 ≤ ((burnsideF48t_g23τ 0 : Fin 728) : ℕ) ∧
    (burnsideF48t_g23σ 0 0 = 0 ∧ burnsideF48t_g23σ 0 364 = 364 ∧
      burnsideF48t_g23σ 1 0 = 0 ∧ burnsideF48t_g23σ 1 364 = 364 ∧
      burnsideF48t_g23σ 2 0 = 0 ∧ burnsideF48t_g23σ 3 364 = 364 ∧
      burnsideF48t_g23σ 3 0 ≠ 0 ∧ burnsideF48t_g23σ 2 364 ≠ 364) ∧
    (∀ s ∈ burnsideF48t_g23S0', s 0 = 0 ∧ s 364 = 364) ∧
    (∀ p : Fin 728, p ≠ 0 → p ≠ 364 → ∃ s ∈ burnsideF48t_g23S0', s p ≠ p) ∧
    (∀ p : Fin 728, 364 ≤ (p : ℕ) → ∃ g ∈ burnsideF48t_g23P1', g p ≠ p) ∧
    ∀ p : Fin 728, (p : ℕ) < 364 → ∃ g ∈ burnsideF48t_g23P2', g p ≠ p := CFSG.KC.G23F48.facts7762

end Certificates
