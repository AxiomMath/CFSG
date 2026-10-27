
module

public import CFSG.CGT.T75JM.N0ModelInputs
public import CFSG.CGT.T75JM.PData
import Certificates.Kernel.T75JM.N0KGlue
import CFSG.Certificates.Kernel.T75JM.PCheckKSound

public section

namespace Certificates

open CFSG.CGT.T75JM CFSG.KC.N0K CFSG.KC.TabWord.M22

open CFSG.CGT.T75JM in
theorem certificate14988 : (n0InvCheck = true) ∧ (n0RelCheck = true) ∧
    ∀ w w' : List (Fin 6 × Bool), n0Tab w = n0Tab w' → val6 w = val6 w' := by
  refine ⟨n0Inv_ok, n0Rel_ok, fun w w' h => ?_⟩
  have e : phiK n0Inv_ok n0Rel_ok (n0 w) = phiK n0Inv_ok n0Rel_ok (n0 w') := by
    refine eq_of_rep_eq (rep_phiK (h1 := n0Inv_ok) (h2 := n0Rel_ok) w) ?_
    rw [h]
    exact rep_phiK (h1 := n0Inv_ok) (h2 := n0Rel_ok) w'
  exact phiK_injective (h2 := n0Rel_ok) letterRd_LP n0Inv_ok n0k_ok e

end Certificates
