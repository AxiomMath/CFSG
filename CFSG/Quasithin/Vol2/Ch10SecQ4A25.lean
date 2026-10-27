module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Final4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4N3Done
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.G3

theorem C10E4.noDelta5Statement_proved
    : NoDelta5Statement := fun Y _ _ hq hS hO =>
  noDelta5_quasisimple Vol2Native.threeCoverFactCat a314ModelFacts
    (((((Delta5Residual7.of_j4 j4Normalizer3).toResidual6).toResidual5).toResidual3).toResidual2
      ).toResidual Y hq hS hO

theorem obl10_2_1E4A314_holds
    (hF1 : FactA314NoSL25Block) (hF2 : FactA314B45)
    (hNq : Obl10_2_1E4Nonquasi) (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hA7 : Ch11.SecA.FactA7Cent) : Obl10_2_1E4A314 :=
  obl10_2_1E4A314_of hF1 hF2 hNq C10E4.noDelta5Statement_proved h113 h37 h38 h318 h36' hA7

end CFSG.Quasithin.Vol2.Ch10.SecF
