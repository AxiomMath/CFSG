module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Base
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface
public import CFSG.Milestones.ASVolI.F48.Small.U42LetterData

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut

@[expose] def burnsideF48s_sp43eG (i : Fin 5) : Ah :=
  ⟨wordAP (burnsideF48s_sp43eXY.getD i []), wordAP_mem _⟩

@[expose] def burnsideF48s_sp43eB : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_sp43eG 0, burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 4}

@[expose] def burnsideF48s_sp43eP1 : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_sp43eG 0, burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 2,
    burnsideF48s_sp43eG 4}

@[expose] def burnsideF48s_sp43eP2 : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_sp43eG 0, burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 3,
    burnsideF48s_sp43eG 4}

@[expose] def burnsideF48s_sp43eK : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_sp43eG 4, burnsideF48s_sp43eG 0 ^ 3}

@[expose] def burnsideF48s_u42eG (i : Fin 5) : Ah :=
  ⟨wordAP (burnsideF48s_u42eXY.getD i []), wordAP_mem _⟩

@[expose] def burnsideF48s_u42eB : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_u42eG 0, burnsideF48s_u42eG 1, burnsideF48s_u42eG 4}

@[expose] def burnsideF48s_u42eP1 : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_u42eG 0, burnsideF48s_u42eG 1, burnsideF48s_u42eG 2,
    burnsideF48s_u42eG 4}

@[expose] def burnsideF48s_u42eP2 : Subgroup Ah :=
  Subgroup.closure {burnsideF48s_u42eG 0, burnsideF48s_u42eG 1, burnsideF48s_u42eG 3,
    burnsideF48s_u42eG 4}

end CFSG.ASVolI
