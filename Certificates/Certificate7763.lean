module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Defs
import Certificates.Kernel.G23F48.Restate
import Certificates.Certificate7761

public section

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7763 : (∀ g ∈ burnsideF48t_g23X, ∀ x : Fin 728, (x : ℕ) < 364 → ((g x : Fin 728) : ℕ) < 364) ∧
    burnsideF48t_g23P1' =
      burnsideF48t_g23X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 728)) (0 : Fin 728) ∧
    burnsideF48t_g23P2' =
      burnsideF48t_g23X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) ∧
    burnsideF48t_g23B' = burnsideF48t_g23P1' ⊓ burnsideF48t_g23P2' ∧
    (∀ R : Subgroup (Equiv.Perm (Fin 728)), burnsideF48t_g23P1' < R → R ≤ burnsideF48t_g23X →
      R = burnsideF48t_g23X) ∧
    (∀ R : Subgroup (Equiv.Perm (Fin 728)), burnsideF48t_g23P2' < R → R ≤ burnsideF48t_g23X →
      R = burnsideF48t_g23X) ∧
    burnsideF48t_g23B' ≤
      Subgroup.normalizer (burnsideF48t_g23S0' : Set (Equiv.Perm (Fin 728))) :=
  CFSG.KC.G23F48.facts7763 certificate7761.1

end Certificates
