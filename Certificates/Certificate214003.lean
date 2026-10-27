module

public import CFSG.LieType.ChevTwo.OppCl.SmallU33Check
import CFSG.Certificates.Kernel.PermCent.U33Sound
import Certificates.Kernel.PermCent.KU33

public section

open CFSG.Certificates.Kernel.PkCV.U33T

namespace Certificates

open CFSG.LieType.ChevTwo.OppCl.U33Fin in
theorem certificate214003 : (checkCenter () = true)
    ∧ (checkExp () = true)
    ∧ (checkF1 () = true)
    ∧ (checkF3 () = true)
    ∧ (checkX5 () = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [center_eq]
    exact kCenter
  · rw [exp_eq]
    exact kExp
  · rw [f1_eq]
    exact kF1
  · rw [f3_eq]
    exact kF3
  · rw [x5_eq]
    exact kX5

end Certificates
