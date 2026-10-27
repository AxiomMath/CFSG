module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestOuter
public import CFSG.LocalAnalysis.StandardType.GGD4FieldAutMaximalTransport
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCoatom
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.SeitzGeneration.ExcWideThree

section Holds

theorem ggD4FieldAutMaximalInput_holds :
    GGD4FieldAutMaximalInput := by
  rintro ⟨d, hv⟩ q hd hq3 hq3a _ _ _ E hE hcard hEI
  have hd' : d = TauCeti.LieTypeIndex.D 4 q := hd
  subst hd'
  obtain ⟨K, _, _, hK, hKchar, ⟨φ⟩⟩ := exists_catEquiv_D4 q hv
  haveI : CharP K 3 := hq3 ▸ hKchar
  have hK3 : Nat.card K = 3 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq3]
  exact ggD4FieldAutMaximal_transport φ
    (fun E' hE' hc' hEI' => d4_fieldAutMaximal_model hK3 hE' hc' hEI') E hE hcard hEI

end Holds

end CFSG.StandardType
