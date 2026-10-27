module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10065.json.gz" 31713 17653933558454885059
  (P65 : List (List (Nat × Nat))) (R65 : List Nat) (RT65 : List Nat) (G65 : List Nat)

@[expose] def ksTxt65 : String := include_str "D10065/ks.hex"

@[expose] noncomputable def ksL65 : Nat → Nat := by hex_tree ksTxt65 20736 13690884063694919939 576

end CFSG.KD.Co1M

end
