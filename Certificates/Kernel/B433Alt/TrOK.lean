module

public import Certificates.Data.Kernel.B433Alt.Trace
public import Certificates.Kernel.B433Alt.Data.St
public import CFSG.Monster.Existence.TwoPoint.B433CoverData
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B4AT "Certificates/Kernel/B433Alt/Data/tr.json.gz" 26582 16887386420331942557
  (K0 : List Nat) (A0 : List Nat) (J : List Nat) (K1 : List Nat) (A1 : List Nat) (TQ : List Nat)
  (PA : List Nat)

namespace CFSG.KD.B4AT

open CFSG.KC.B4A CFSG.Monster.Existence.B433Cover

@[expose] def trWord (l : Nat) : List Nat := nodeWord l ++ 10 :: (nodeWord l).reverse

@[expose] noncomputable def trChk (i : Nat) : Bool :=
  trOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW (nat_lit 5965) (K0.getD i 0)
    (A0.getD i 0) (trWord (i + 1)) (J.getD i 0) (K1.getD i 0) (A1.getD i 0)

end CFSG.KD.B4AT

end
