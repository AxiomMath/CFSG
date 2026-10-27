module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.LieType.Catalog.Realization

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem d4_isSimpleGroup : IsSimpleGroup D := by
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 D' hD'
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple D' .trialityD4 0 2 1 hD'
  exact e.symm.isSimpleGroup

end CFSG.Quasithin.D4Hex
