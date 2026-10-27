module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitE6ThreeAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeSplitOn_e6Three :
    GGNbrTableBWeylTypeSplitOn fun p lab => lab.tag = .E6 ∧ p = 3 := by
  intro p hp hp2 lab hlab hS hhs hsp
  obtain ⟨htag, rfl⟩ := hS
  intro Q hQ
  have h3 : 3 ∣ 2 ^ lab.n - 1 := hsp.2.2
  have h := largeEvenLabelAll_e6Div_of (P := fun R _ I => GGTorusWeylTypeW 3 5 R I)
    htag hlab h3 (fun K _ _ n hn hK h3' =>
      ggWTSE6_weylTypeW_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.1 K n hn hK h3'))
  exact largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, 5, hh.2.1, hh.2.2⟩) (h Q hQ)

end CFSG.StandardType

end
