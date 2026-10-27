module

import CFSG.GH74.Filter.Sporadic.BMax2
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace Certificates

theorem certificate5023 : ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.B,
    CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 :=
  CFSG.GH74.Filter.exists_E32_B_of_max2

end Certificates
