
module

public import CFSG.Sporadic.J4.QT2LocCntProofBase

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem length_zMasks : zMasks.length = 1771 := chkZMasks_parts.2.1

theorem nodup_zMasks : zMasks.Nodup := chkZMasks_parts.2.2.1

theorem three_mem_zMasks :
    (3 : ℕ) ∈ zMasks := chkZMasks_parts.2.2.2.1

theorem mem_zMasks_1131 :
    (1131 : ℕ) ∈ zMasks := chkZMasks_parts.2.2.2.2.1

end CFSG.Sporadic.J4.QT2
