
module

import Certificates.Kernel.He7030.HeB
public import CFSG.Sporadic.He.Setup

public section

public section

namespace Certificates

theorem certificate589204 : 
    ∀ U : Subgroup CFSG.Sporadic.He.J, Nat.card U = 2 ^ 10 * 3 ^ 2 →
      ∃ Y : Subgroup CFSG.Sporadic.He.J, Y ≤ U ∧ (Y.subgroupOf U).Normal ∧ Nat.card Y = 2 ^ 6 * 3 ∧
        Y ≤ Subgroup.closure {x | x ∈ U ∧ Odd (orderOf x)} := by
  exact CFSG.KD.He7030.heSubO2_JK

end Certificates

end

end
