module

public import CFSG.Quasithin.Vol2.KGFactE64L52
public import CFSG.Quasithin.Vol2.KGFactE64M24
public import CFSG.Quasithin.Vol2.KGFactE64He

public section

namespace CFSG.Quasithin.H13.KGE64

theorem heInspE64_holds :
    HeInspE64 :=
  ⟨fun _ _ _ hX => not_heInspCfg_l52 hX, not_heInspCfg_m24, not_heInspCfg_he⟩

end CFSG.Quasithin.H13.KGE64
