module

public import CFSG.Quasithin.H13.A5S1327za

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

@[expose] noncomputable def G0e (H : Subgroup G) : Subgroup G := S.G1e H ⊔ S.G2e

include S

end Setting

end CFSG.Quasithin.H13.A5
