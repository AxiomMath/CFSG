module

public import Certificates.Data.CFSGNative.Co1Schreier.Base
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

set_option maxHeartbeats 2000000

namespace CFSG.KD.Co1P

#kc_repo #kc_json_gz CFSG.KD.Co1P
  "Certificates/Kernel/Co1P/data/DagData.json.gz" 104695 3874604992610171793
  (BRS59 : List Nat) (BRIS59 : List Nat) (GDS : List Nat) (GDIS : List Nat) (GWN : List (List Nat))

@[expose] noncomputable def GWL : List (List Int) := GWN.map CFSG.Sporadic.Co1Schreier.Native.decWord

end CFSG.KD.Co1P

end
