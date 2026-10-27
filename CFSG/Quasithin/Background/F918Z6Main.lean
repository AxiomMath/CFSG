module

public import CFSG.Quasithin.Background.F918Z6Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem d37_of_z37 (hL38 : D3L38) (hA21 : AsA21SQTKSection)
    (hZ1 : Z1Stmt) (hMain : Z37Main) : D37 := by
  intro W _ _ M Mp T L V hD hVT t htT htL hMp
  have n := D37Cfg.of_d3L38 hL38 hD hVT htT htL hMp
  have hc := hMain ↥V _ _ _ _ _ (z37_of_cfg hA21 hZ1 n)
  unfold Z37Concl at hc
  rw [n.sup_eq] at hc
  exact hc

end CFSG.Quasithin
