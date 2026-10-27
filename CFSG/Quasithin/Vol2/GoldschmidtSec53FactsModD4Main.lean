module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYam
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Setup.X6

set_option linter.unusedSectionVars false


theorem lieModelFacts_d4 : LieModelFacts .trialityD4 0 :=
  Yam.lieModelFacts_of_std fun Y _ f hpar hY => by
    obtain ⟨-, hX⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hY (by decide)
    obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    exact ⟨_, inferInstance, inferInstance, _, _, _,
      CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσ,
      TriD4.d4_lieFactsOf σ hpar.1 hK hσ, ⟨e⟩⟩

end CFSG.Quasithin.H13.Sec53F
