module

public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
import Certificates.Kernel.IdxFour.E0Chain

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17601 : Nat.card E0 = 9797760 ∧
    ∀ U ∈ E0, (∀ b ∈ [12, 20, 264, 36, 63], U (vecOf b) = vecOf b) → U = 1 :=
  ⟨CFSG.KD.IF4E.card_E0, fun _ hU hfix => CFSG.KD.IF4E.eq_one_of_fix_base hU hfix⟩

end Certificates
