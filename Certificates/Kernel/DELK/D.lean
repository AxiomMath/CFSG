module

public import Certificates.Data.Kernel.DELK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.DELK in
#kc_repo #kc_json_gz CFSG.KD.DELK "Certificates/Kernel/DELK/data/d.json.gz" 17265
  2379511506652140526
  (O : List KPat1) (T : List KPat2) (H : List KHK) (Z : List KPZ) (P : List (List GGDepANPair))
  (S : List KBase) (C : List KConj)

end
