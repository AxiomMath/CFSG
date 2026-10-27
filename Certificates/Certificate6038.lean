module

public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeInputs
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
import Certificates.Kernel.StdOdd.SylowThree

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley in
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel in
open CFSG.Monster.B.Classical.E6Adjoint in
open CFSG.Monster.Existence.StdOdd.P5 (E5 GL5 M5 rk refl reflGL genA genB Pbar IsExt) in
theorem certificate6038 : (CertNative.fixedOK bracketCodes formBits gamTable
      ((List.range 6).map rWord) = true)
    ∧ (∀ i < 6, ∀ l ∈ rWord i, l.1 < 72)
    ∧ (CertNative.conjOK bracketCodes formBits ((List.range 6).map rWord)
      ((List.range 5).map eWord) colsData = true)
    ∧ (∀ (i : Fin 6) (j : Fin 5), colsData.getD (5 * i + j) [] =
      [(colVec i j 0).val, (colVec i j 1).val, (colVec i j 2).val, (colVec i j 3).val,
        (colVec i j 4).val])
    ∧ (CertNative.splitOK bracketCodes formBits ((List.range 6).map rWord)
      tAidx tBidx pwData raData rbData = true)
    ∧ (P5.pw 0 = []) := CFSG.KD.StdOdd.SylowThree.facts

end Certificates
