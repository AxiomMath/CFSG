module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

abbrev str86U (L1 L2 S : Subgroup G) : Subgroup G := conjClosure (Z1 L1 L2 S) (L2 ⊔ S)

end CFSG.Quasithin.Stroth
