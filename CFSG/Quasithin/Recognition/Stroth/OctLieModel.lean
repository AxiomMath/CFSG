module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.LieType.ChevTwo.ReeGammaLieModel
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadical

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.Quasithin.H13.F431.TwoF4


theorem octLieModel : OctLieModel := by
  intro K _ _ _ a ha hK
  refine Or.inr ⟨by omega, ⟨a, by ring⟩, ?_⟩
  exact CFSG.LieType.ChevTwo.Semi.lieModel_reeGamma K a ha hK

end CFSG.Quasithin.Stroth
