module

public import Certificates.Data.Kernel.B433Alt.Lab
public import Certificates.Kernel.B433Alt.Data.St
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B4AL "Certificates/Kernel/B433Alt/Data/lab.json.gz" 383213 7585553527195000511
  (LN : List Nat) (LJ : List Nat) (LA : List Nat) (LPt : List Nat) (LG : List Nat) (LNG : List Nat)
  (LO : List Nat) (LW : List (List Nat)) (LC : List (List (Nat × Nat)))

namespace CFSG.KD.B4AL

@[expose] noncomputable def labChk (i : Nat) : Bool :=
  CFSG.KC.B4A.labOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW (nat_lit 5965)
    (LN.getD i 0) (LW.getD i []) (LJ.getD i 0) (LA.getD i 0) (LPt.getD i 0) (LG.getD i 0)
    (LNG.getD i 0) (LC.getD i []) (LO.getD i 0)

end CFSG.KD.B4AL

end
