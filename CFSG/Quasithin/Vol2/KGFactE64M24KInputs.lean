module

public import CFSG.Quasithin.Vol2.KGFactE64M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs

public section

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24

namespace CFSG.Quasithin.H13.KGE64

@[expose] def m24E64K : Prop :=
  e64Check 24 (List.range 24) (codeSetAct 24) (m24LatK.sTabs ++ m24LatK.mt[1]!).toArray
      m24E64Y1 m24E64O1 m24LatK.Om[1]!.lbl.toList = true ∧
    e64Check 24 (List.range 24) (codeSetAct 24) (m24LatK.sTabs ++ m24LatK.mt[2]!).toArray
      m24E64Y2 m24E64O2 m24LatK.Om[2]!.lbl.toList = true ∧
    e64Check 24 (List.range 24) (codeSetAct 24) (m24LatK.sTabs ++ m24LatK.mt[4]!).toArray
      m24E64Y4 m24E64O4 m24LatK.Om[4]!.lbl.toList = true ∧
    e64Check 24 (List.range 24) (codeSetAct 24) (m24LatK.sTabs ++ m24LatK.mt[6]!).toArray
      m24E64Y6 m24E64O6 m24LatK.Om[6]!.lbl.toList = true

end CFSG.Quasithin.H13.KGE64
