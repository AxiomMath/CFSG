module

public import CFSG.F3.Spec
public import Certificates.Data.CFSGNative.ON.Data
public import Certificates.Data.CFSGNative.F3.Basic
import CFSG.Certificates.Kernel.Spor.F3LaneEq
import Certificates.Kernel.SporDet.ONData
import Certificates.Data.Kernel.Spor.F3LaneId
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.ON

open CFSG.Blueprint.NativeSporadic CFSG.F3.Native

private theorem seedA_eq : Native.seedA = ONSeed1 := rfl

private theorem seedB_eq : Native.seedB = ONSeed2 := rfl

private theorem rowsOf_size (s : String) : (rowsOf 154 s).size = 154 := by
  unfold rowsOf; simp

end CFSG.Sporadic.ON
