module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Data
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ASVolI

open CFSG.CosetTable

abbrev burnsideF48t_g23Ws : List (List (Fin 4 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_g23R1 burnsideF48t_g23R2 6 [(2, true)] [(3, true)] []

abbrev burnsideF48t_g23WsB : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) burnsideF48t_g23Ws

end CFSG.ASVolI
