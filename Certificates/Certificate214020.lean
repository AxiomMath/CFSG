module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Check
import CFSG.Certificates.Kernel.PermCent.U33Sound
import Certificates.Kernel.PermCent.KU33

public section

open CFSG.Certificates.Kernel.PkCV.U33T

namespace Certificates

open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin in
theorem certificate214020 : (checkT0 () = true) ∧ (checkZ () = true) ∧ (checkC () = true) ∧ (checkE1 () = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [t0_eq]
    exact kT0
  · rw [z_eq]
    exact kZ
  · rw [c_eq]
    exact kC
  · rw [e1_eq]
    exact kE1

end Certificates
