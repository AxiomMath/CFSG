module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6ThreeAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTwE6ThreeNbrWeylTypeInput_holds :
    GGTwE6ThreeNbrWeylTypeInput := by
  intro lab hlab hbad
  have h := largeEvenLabelAll_twE6Three_of (p := 3) hlab hbad
    (P := fun R _ I => GGTorusWeylTypeW 3 5 R I)
    (fun K _ _ n hn hK h3 =>
      ggWTT3_weylTypeW_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.2 K n hn hK h3))
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, hh.2.2⟩) (h Q hQ)

end CFSG.StandardType

end
