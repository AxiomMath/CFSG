module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
import Certificates.Kernel.BalanceSC.Glue

public section

namespace Certificates

open CFSG.OddStandard.Solomon75.AhatData in
theorem certificate6120 : Nat.card (P0 9) = 64 ∧ SylowGood 9 (P0 9) ∧ BalanceGood 9 3 (P0 9) :=
  ⟨CFSG.KD.BalSC9.card_sylow.1, CFSG.KD.BalSC9.card_sylow.2, CFSG.KD.BalSC9.balance⟩

end Certificates
