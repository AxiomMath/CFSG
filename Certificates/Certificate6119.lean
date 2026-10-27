module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
import Certificates.Kernel.BalanceSC.Glue

public section

namespace Certificates

open CFSG.OddStandard.Solomon75.AhatData in
theorem certificate6119 : Nat.card (P0 8) = 64 ∧ SylowGood 8 (P0 8) ∧ BalanceGood 8 3 (P0 8) :=
  ⟨CFSG.KD.BalSC8.card_sylow.1, CFSG.KD.BalSC8.card_sylow.2, CFSG.KD.BalSC8.balance⟩

end Certificates
