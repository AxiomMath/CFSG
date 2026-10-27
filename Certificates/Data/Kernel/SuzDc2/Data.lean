module

public import Certificates.Data.Kernel.SporLatDc2
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.SLD2

#kc_repo #kc_json_gz CFSG.KD.SuzDc2.J "Certificates/Data/Kernel/SuzDc2/data/dc2.json.gz" 1264298
  10758398941686638736
  (sep : List Nat) (pw : Nat) (bo : List BOrb) (R1 : List Rec1) (fB : Nat)
  (fC : List (List (List Nat))) (fw : Nat) (fpc : List Nat) (fpar : List Nat) (fvia : List Nat)
  (ford : List Nat) (R2 : List Rec2) (gw : Nat) (gd : Nat) (roots : List (List Root))

#kc_repo #kc_json_gz CFSG.KD.SuzDc2.LT "Certificates/Data/Kernel/SuzDc2/data/letters.json.gz"
  1033637 5303738633991477795
  (lc : List Nat) (sgw : List (List Nat)) (hw : List Nat)

set_option maxRecDepth 10000 in
#kc_repo #kc_json_gz CFSG.KD.SuzDc2.SB "Certificates/Data/Kernel/SuzDc2/data/sb.json.gz" 581003
  13260989677943468457
  (B : Nat) (C : List (List (List Nat))) (rows : List (List Nat)) (par : List Nat)
  (via : List Nat) (ord : List Nat)
