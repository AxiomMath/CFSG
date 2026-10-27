module

public import Certificates.Data.Kernel.B433Alt.Arith
public import Certificates.Kernel.B433Alt.Data.Ch
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B4AR "Certificates/Kernel/B433Alt/Data/arith.json.gz" 6052 9009012864013042058
  (idx : List Nat) (F : List (Nat × Nat)) (A : List Nat) (M : List Nat)

namespace CFSG.KD.B4AR

@[expose] noncomputable def wv (j : Nat) : Nat := 4089470473293004800 / CFSG.KD.B4AC.MJ j

@[expose] noncomputable def arChk (k : Nat) : Bool :=
  CFSG.KC.B4A.ssChk wv idx F A 1015970529280000 (M.getD k 0) k

end CFSG.KD.B4AR

end
