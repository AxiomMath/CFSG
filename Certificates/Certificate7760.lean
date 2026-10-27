module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Defs
import Certificates.Kernel.G23F48.Restate

public section

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7760 : (∀ i < 728, ((burnsideF48t_g23Pts ())[i]!).size = 14 ∧
      (((burnsideF48t_g23Pts ())[i]!).all fun x => decide (x < 3)) = true ∧
      ((burnsideF48t_g23Pts ())[i]!).find? (· != 0) = some 1) ∧
    (∀ i < 728, ∀ l < 728, (burnsideF48t_g23Pts ())[i]! = (burnsideF48t_g23Pts ())[l]! → i = l) ∧
    (∀ i < 728, ∀ l < 728,
      (burnsideF48t_g23Pts ())[i]! ≠ ((burnsideF48t_g23Pts ())[l]!).map fun x => 2 * x % 3) ∧
    ∀ k < 4, ∀ i : Fin 728, (burnsideF48t_g23Pts ())[((burnsideF48t_g23γ k i : Fin 728) : ℕ)]! =
      burnsideF48t_g23Norm
        (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[k]! (burnsideF48t_g23Pts ())[(i : ℕ)]!) := CFSG.KC.G23F48.facts7760

end Certificates
