module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Geom
public import CFSG.Milestones.ASVolI.F48.Small.U42LetterData

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42

@[expose] def burnsideF48s_sp43G (i : Fin 4) : Y :=
  ⟨wordP (burnsideF48s_sp43XY.getD i []), wordP_mem _⟩

@[expose] def burnsideF48s_sp43B : Subgroup Y :=
  Subgroup.closure {burnsideF48s_sp43G 0, burnsideF48s_sp43G 1}

@[expose] def burnsideF48s_sp43P1 : Subgroup Y :=
  Subgroup.closure {burnsideF48s_sp43G 0, burnsideF48s_sp43G 1, burnsideF48s_sp43G 2}

@[expose] def burnsideF48s_sp43P2 : Subgroup Y :=
  Subgroup.closure {burnsideF48s_sp43G 0, burnsideF48s_sp43G 1, burnsideF48s_sp43G 3}

@[expose] def burnsideF48s_sp43K : Subgroup Y :=
  Subgroup.zpowers (burnsideF48s_sp43G 0 ^ 3)

end CFSG.ASVolI
