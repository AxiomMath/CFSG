module

public import CFSG.Quasithin.Background.RonanH163Chain
public import CFSG.Quasithin.Background.RonanH163Transv
public import CFSG.Quasithin.Background.RonanH163Beta
public import CFSG.Quasithin.Background.RonanH163Cen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem std163 :
    Concl163 R Qstd :=
  ⟨⟨U8, U9, chain_std, fullTransp_std⟩, induces_std, cen_std⟩

end CFSG.Quasithin.RonanH163
