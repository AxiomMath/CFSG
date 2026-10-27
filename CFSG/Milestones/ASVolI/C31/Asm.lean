module

public import CFSG.Milestones.ASVolI.C31.Inputs
public import CFSG.Quasithin.Background.C31AsmPf

public section

namespace CFSG.ASVolI

theorem burnsideC31_as_C_3_1_of_KW
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : C_3_1 := by
  intro G _ _
  have hA37 := CFSG.Quasithin.H13.a3ForSQTK_holds.1
  have hA38 := CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  exact CFSG.Quasithin.C31.asc31Statement_of_inputs CFSG.Quasithin.H13.VolI.a36ForSQTK_holds hA37
    hA38 (CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38) (burnsideC31_outSolvable G)
    burnsideC31_inspC33 (burnsideC31_inspC31Sporadic_of_KW hKW) (burnsideC31_c31LieStep G)

theorem burnsideC31_inspC31Sporadic_of_J4
    (hJ4 : CFSG.Quasithin.InspC31SporadicAtJ .J4) : CFSG.Quasithin.InspC31Sporadic :=
  CFSG.Quasithin.KGC31.inspC31Sporadic_of CFSG.Quasithin.KGC31.Ru.inspC31SporadicAt_ru hJ4

end CFSG.ASVolI
