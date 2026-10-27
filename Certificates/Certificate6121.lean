module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
import Certificates.Kernel.BalanceSC.Glue

public section

namespace Certificates

open CFSG.OddStandard.Solomon75.AhatData in
theorem certificate6121 : Nat.card (P0 10) = 128 ∧ SylowGood 10 (P0 10) ∧ BalanceGood 10 3 (P0 10) :=
  ⟨CFSG.KD.BalSC10.card_sylow.1, CFSG.KD.BalSC10.card_sylow.2, CFSG.KD.BalSC10.balance⟩

end Certificates
