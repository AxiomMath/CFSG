module

public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.Quasithin.EmptyFaithful.S1417Final

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace S1417

theorem stageLemma1417Stab_of_stageLemma1416 (h16 : StageLemma1416) : StageLemma1417Stab := by
  intro G _ _ T Mc h M V hM hV hJ hcase
  exact stab_of_core h hM hV hJ hcase fun V' hV' => (h16 G T Mc h).1 M V' hM hV'

end S1417

end CFSG.Quasithin
