module

public import CFSG.Quasithin.H13.KGFactT3J4Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs

public section

namespace CFSG.Quasithin.H13.KGT3J4

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24

@[expose] def T3J4LatK : Prop :=
  ∀ j < 13, m24LatK.Om[j]!.lbl.size = 9 →
    (∃ x < m24LatK.Om[j]!.lbl.size,
      codeSetAct 24 t3yTab m24LatK.Om[j]!.lbl[x]! = codeSetAct 24 t3cTab t3yLab) →
    GensIn (codeSetAct 24) m24Delta m24LatK j 2

end CFSG.Quasithin.H13.KGT3J4
