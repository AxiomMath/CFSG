module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CFSG.Sporadic.Co1Schreier.RecData

#kc_repo #kc_json_gz CFSG.Sporadic.Co1Schreier.RecData
  "CFSG/Sporadic/Schreier/Data/co1-cert-orbits.json.gz" 578599 7499698994233927500
  (o0 : List Nat) (o1 : List Nat) (o2 : List Nat) (o3 : List Nat)

#kc_repo #kc_json_gz CFSG.Sporadic.Co1Schreier.RecData
  "CFSG/Sporadic/Schreier/Data/co1-cert-merges.json.gz" 3283775 15023569460192625957
  (m0 : List Nat) (m1 : List Nat) (m2 : List Nat)

@[expose] def triple (x : Nat) : List Nat := [x % 2, x / 2 % 98280, x / 196560]

end CFSG.Sporadic.Co1Schreier.RecData
