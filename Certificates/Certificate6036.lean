module

public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
import Certificates.Kernel.StdOdd.Reps

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std in
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel in
theorem certificate6036 : (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord5) 5 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord7A) 7 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord7B) 7 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord11) 11 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord13) 13 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord17) 17 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord19) 19 = true) := CFSG.KD.StdOdd.Reps.facts

end Certificates
