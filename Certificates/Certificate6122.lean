module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
import Certificates.Kernel.BalanceSC.Glue

public section

namespace Certificates

open CFSG.OddStandard.Solomon75.AhatData in
theorem certificate6122 : Nat.card (P0 11) = 128 ∧ SylowGood 11 (P0 11) ∧ BalanceGood 11 5 (P0 11) :=
  ⟨CFSG.KD.BalSC11.card_sylow.1, CFSG.KD.BalSC11.card_sylow.2, CFSG.KD.BalSC11.balance⟩

end Certificates
