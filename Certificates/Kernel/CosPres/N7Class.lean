module

public import Certificates.Data.Kernel.N7ModClass
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KernelN7
  "Certificates/Kernel/CosPres/data/n7class.json.gz" 8014 1299105999372797068
  (invL : List Nat) (relL : List Nat)

namespace CFSG.KernelN7

theorem invAll7_ok : invAll7 invL = true := by quickRfl

theorem relAll70_ok : relAll7 0 relL = true := by quickRfl

theorem relAll71_ok : relAll7 1 [] = true := by quickRfl

end CFSG.KernelN7
