
module


public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
import Certificates.Kernel.Misc.E6StdBridge

public section

namespace Certificates

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint in
theorem certificate10004 :
    (Native.check bracketCodes formBits fwdProg idxA CFSG.LieType.Chevalley.C2E6Std.MatrixModel.idxB bwdProg letterIdx = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2
          [(0, true), (1, true), (0, true), (1, true), (1, true)]) 5 = true) := CFSG.KD.Misc.E6Std.facts

end Certificates
