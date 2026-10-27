module

public import Certificates.Data.Kernel.E64L
public import Certificates.Data.Kernel.M24Dc.Defs
public import CFSG.Quasithin.Vol2.KGFactE64M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs

public noncomputable section

namespace CFSG.KD.M24Dc

open CFSG.KC.E64L CFSG.Quasithin.H13.KGE64

@[expose] def e64J : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 6

@[expose] def e64Y : Nat → List Nat
  | 0 => m24E64Y1
  | 1 => m24E64Y2
  | 2 => m24E64Y4
  | _ => m24E64Y6

@[expose] def e64O : Nat → List (List Nat)
  | 0 => m24E64O1
  | 1 => m24E64O2
  | 2 => m24E64O4
  | _ => m24E64O6

@[expose] noncomputable def ltL (j : Nat) : List (List Nat) :=
  [J.tabs.getD 2 [], J.tabs.getD 3 [], J.tabs.getD 4 [], J.tabs.getD 5 []] ++
    (J.mw.getD j []).map (wordTabT [J.tabs.getD 0 [], J.tabs.getD 1 []] 24)

@[expose] noncomputable def e64M (i : Nat) : Bool :=
  e64CheckT 24 (List.range 24) (codeSetTL 24) (ltL (e64J i)) (e64Y i) (e64O i)
    (Om (e64J i)).lbl.toList

end CFSG.KD.M24Dc

end
