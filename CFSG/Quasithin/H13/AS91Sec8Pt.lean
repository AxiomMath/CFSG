module

public import CFSG.Quasithin.H13.AS91Sec5Geom

public section

namespace CFSG.Quasithin.H13.AS91

variable {G : Type*} [Group G]

abbrev basePt (A : Subgroup G) : G ⧸ A := ((1 : G) : G ⧸ A)

end CFSG.Quasithin.H13.AS91
