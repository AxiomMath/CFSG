module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Defs
import Certificates.Kernel.G23F48.Restate
import Certificates.Certificate7761

public section

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7764 : (∀ c ∈ burnsideF48t_g23K', c = 1 ∨ c = burnsideF48t_g23κ 0 ∨ c = burnsideF48t_g23κ 1 ∨
      c = burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) ∧
    (∀ x ∈ burnsideF48t_g23P1', x ∉ burnsideF48t_g23P2' →
      (∀ k ∈ burnsideF48t_g23K', x * k * x⁻¹ ∈ burnsideF48t_g23K') →
      (burnsideF48t_g23σ 2)⁻¹ * x ∈ burnsideF48t_g23K') ∧
    ∀ y ∈ burnsideF48t_g23P2', y ∉ burnsideF48t_g23P1' →
      (∀ k ∈ burnsideF48t_g23K', y * k * y⁻¹ ∈ burnsideF48t_g23K') →
      (burnsideF48t_g23σ 3)⁻¹ * y ∈ burnsideF48t_g23K' :=
  CFSG.KC.G23F48.facts7764 certificate7761.1

end Certificates
