module

public import CFSG.Quasithin.Background.F918T5
public import CFSG.Quasithin.Background.F918T7
public import CFSG.Quasithin.Background.F918T8

public section

namespace CFSG.Quasithin

theorem d35InspExtSq_of_U (hU : D35InspExtSqU) : D35InspExtSq :=
  d35InspExtSq_of_unitri (fun _ hE => exists_conj_le_unitri5 hE) hU

theorem d35InspUniq_of_U (h8 : D35InspUniq8) (hU : D35InspExtSqU) : D35InspUniq :=
  d35InspUniq_of_inputs h8 (d35InspExtSq_of_U hU)

end CFSG.Quasithin
