module

public import CFSG.Quasithin.H13.A5S1327za

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

include S

theorem e1_mem_T0e : S.e1 ∈ S.T0e :=
  ⟨S.V_le_T S.e1_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr
    (B2F.isElemAbelian_comm S.elemAbelian_V S.e1_mem_V S.e2_mem_V)⟩

end Setting

end CFSG.Quasithin.H13.A5
