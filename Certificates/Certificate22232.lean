module

public import Certificates.Data.GrSLitL34FactsCF23ONOutK2Data
import Certificates.Kernel.ONOut.Out2
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.ONOut.Data

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.ONOut CFSG.F3.Native CFSG.Sporadic.ON.Native in
theorem certificate22232 :
    (okRows rRows && (mulVecRow wRows vVec).beq V.zero &&
      eqM 154 (addM (CFSG.F3.Native.mul 154 rRows wRows) (outerRows vVec uVec)) (CFSG.F3.Native.idM 154)) = true ∧
    (spinRows.size == 154 && spinRows[0]!.beq vVec &&
      (List.range 153).all (fun t => decide (spinPar[t + 1]! < t + 1) &&
        decide (spinLab[t + 1]! < 2) &&
        spinRows[t + 1]!.beq (mulVecRow (spinGen spinLab[t + 1]!) spinRows[spinPar[t + 1]!]!)) &&
      okRows spinInvRows && eqM 154 (CFSG.F3.Native.mul 154 spinInvRows spinRows) (CFSG.F3.Native.idM 154)) = true ∧
    eqM 154 n0SqRows negIdRows = true := KernelONOut.facts22232

end Certificates
