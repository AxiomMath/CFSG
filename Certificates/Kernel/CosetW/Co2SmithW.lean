module

public import CFSG.Sporadic.Co2Smith.GlWInputs
public import Certificates.Data.Kernel.CosetW.EnumW
public import CFSG.Certificates.CosetTableColumns

public section

set_option maxRecDepth 400000
set_option profiler true

open CFSG.CosetTable CFSG.Sporadic.Co2Smith.Native

namespace CertificateChecks.CosetW

@[expose] def glWR6 : List (List (Fin 6 × Bool)) :=
  restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) glWRels

set_option maxHeartbeats 0 in
theorem glW_e1_checkW : checkW (mkParamsW (cols glWR6).length (colInv glWR6)
    (colCodes glWR6 glWR6) (colCodes glWR6 ((subsetOf 6 []).map fun x => [(x, true)])))
    100000 1440 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem glW_e2_checkW : checkW (mkParamsW (cols glWRels).length (colInv glWRels)
    (colCodes glWRels glWRels)
    (colCodes glWRels ((subsetOf 7 [0, 1, 2, 3, 4, 5]).map fun x => [(x, true)])))
    100000 36 = true := by
  decide +kernel

end CertificateChecks.CosetW
