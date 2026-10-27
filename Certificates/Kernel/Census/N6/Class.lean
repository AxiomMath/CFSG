module

public import Certificates.Data.Kernel.N6ModClass
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KernelN6
  "Certificates/Kernel/Census/N6/data/n6class.json.gz" 8014 10096548783626613819
  (invL : List Nat) (relL : List Nat)

namespace CFSG.KernelN6

theorem invAll_ok : invAll invL = true := by quickRfl

theorem relAll0_ok : relAll 0 relL = true := by quickRfl

theorem relAll1_ok : relAll 1 [] = true := by quickRfl

end CFSG.KernelN6
