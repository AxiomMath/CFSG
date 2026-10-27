module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniR
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniConfig

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces


theorem q1UnitaryTorsion_holds : Q1UnitaryTorsion :=
  q1On_of_selectedTransfer
    (q1SelectedTransfer_of_toral
      (q1ToralActionTransfer_of_rToral
        (q1RToralTransfer_mono (fun _ _ h => uniOdd_of_unitaryTorsion h) q1RToral_uni))
      q1TorUni_config)

end CFSG.StandardType
