
module

public import CFSG.Sporadic.Co2Schreier.SylowCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Kernel.SporSch.Co2M.FratPG
import Certificates.Kernel.SporSch.Co2M.Neg2059
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

namespace Certificates

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co2Schreier

theorem unique_ok : allN 5 (fun k => allN 32 fun w =>
    (w == 2 ^ k || profTable.getD w [] != profTable.getD (2 ^ k) [])) = true := by
  quickRfl

theorem unique_check : uniqueOK profTable = true := by
  unfold uniqueOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k hk
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro w hw
  exact allN_spec (allN_spec unique_ok k hk) w hw

end Certificates
