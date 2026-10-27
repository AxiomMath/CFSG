module

public import CFSG.Quasithin.Recognition.Stroth.SubconstNaturalSz
public import CFSG.Quasithin.Recognition.Stroth.SubconstNaturalL2
public import CFSG.Quasithin.Recognition.Stroth.SubconstNaturalU3

public section

namespace CFSG.Quasithin.Stroth

theorem subconstNatural : SubconstNatural := by
  refine ⟨card_eq_of_hasNormalCopy_sz, card_eq_of_hasNormalCopy_psl2, card_eq_of_hasNormalCopy_psu3⟩

end CFSG.Quasithin.Stroth
