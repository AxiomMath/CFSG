module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9AGen

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

namespace S35.N9

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim9T (hS : Sit H M S) (hII : CaseII H M) (h6b : Claim6b H M)
    (hNb : S35.II.NbarThat H M) (h3a : S35.II.Claim3a H M) : S35.II.Claim9T H M :=
  claim9T_core hS hII h6b hNb h3a fun hD hW hi => gen_of_two_group hD hW hi

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin
