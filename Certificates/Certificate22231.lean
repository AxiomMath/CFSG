module

public import Certificates.Data.GrSLitL34FactsCF23ONOutK1Data
import Certificates.Kernel.ONOut.Out1
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.ONOut.Data1

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.ONOut CFSG.F3.Native CFSG.Sporadic.ON.Native in
theorem certificate22231 :
    (okRows n0Rows && okRows n0InvRows && eqM 154 (CFSG.F3.Native.mul 154 n0Rows n0InvRows) (CFSG.F3.Native.idM 154)) = true ∧
    ((List.range 7).all fun j =>
      okRows sIRows[j]! && eqM 154 (CFSG.F3.Native.mul 154 sRows[j]! sIRows[j]!) (CFSG.F3.Native.idM 154)) = true ∧
    eqM 154 (CFSG.F3.Native.mul 154 (CFSG.F3.Native.mul 154 n0Rows rowsA) n0InvRows) (wordRows sRows sIRows wA) = true ∧
    eqM 154 (CFSG.F3.Native.mul 154 (CFSG.F3.Native.mul 154 n0Rows rowsB) n0InvRows) (wordRows sRows sIRows wB) = true ∧
    eqM 154 (CFSG.F3.Native.mul 154 n0Rows zRows) (CFSG.F3.Native.mul 154 zRows n0Rows) = true ∧
    (eqM 154 (CFSG.F3.Native.mul 154 n0SqRows rowsA) (CFSG.F3.Native.mul 154 rowsA n0SqRows) &&
      eqM 154 (CFSG.F3.Native.mul 154 n0SqRows rowsB) (CFSG.F3.Native.mul 154 rowsB n0SqRows)) = true := KernelONOut.facts22231

end Certificates
