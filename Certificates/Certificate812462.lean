
module

public import CFSG.Monster.B.TwoA.Sp8.LagrangianRadical
import Certificates.Kernel.P0Vis.Assembly
public import CFSG.Monster.B.TwoA.Sp8.P0WordsBase

public section

namespace Certificates

open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.Open in
theorem certificate812462 :     ∀ E : Subgroup Dfull, E ≤ PLam lam0 → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14 :=
  fun E hE hEA => CFSG.KD.P0Vis.card_le_P0_kernel E hE hEA

end Certificates
