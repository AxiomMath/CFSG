module

public import Certificates.Certificate9001
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.NativeSporadic CFSG.F3.Native

theorem rows_B_cube :
    eqM 781 (powM 781 (rowsOf 781 Native.seedB) 3) (idM 781) = true := by
  exact Certificates.certificate9001.1

private theorem seedA_eq : Native.seedA = Fi24primeSeed1 := rfl

private theorem seedB_eq : Native.seedB = Fi24primeSeed2 := rfl

end CFSG.Sporadic.Fi24
