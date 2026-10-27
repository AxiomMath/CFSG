module

public import CFSG.Quasithin.Vol2.KGFactC31M24Data
import Certificates.Kernel.KGC31M24.Facts7216
import Certificates.Kernel.KGC31M24.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31FrameCheck
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 in
theorem certificate7216 : ordTest 24 5 x5T = true ∧ ordTest 24 7 x7T = true ∧ ordTest 24 11 x11T = true ∧
    ordTest 24 23 x23T = true ∧
    orbCheck 24 5 invs [x5T] cands5 = true ∧
    orbCheck 24 7 invs [x7T] cands7 = true ∧
    actCheck 24 11 invs [x11T] = true ∧
    actCheck 24 23 invs [x23T] = true ∧
    ((List.range 26).all fun k => CFSG.Sporadic.Th.Native.invOK 24 (candT k) (CFSG.Sporadic.Th.Native.invT 24 (candT k))) = true ∧
    (frameConjT.all fun c => CFSG.Sporadic.Th.Native.invOK 24 c (CFSG.Sporadic.Th.Native.invT 24 c)) = true ∧
    frameCheck 24 7 x7T (CFSG.Quasithin.KGC31.M24.conjAll (candT 12) u5T) (frameVs 12) (frameCands fr0W) = true ∧
    frameCheck 24 7 x7T (CFSG.Quasithin.KGC31.M24.conjAll (candT 17) u5T) (frameVs 17) (frameCands fr1W) = true ∧
    frameCheck 24 7 x7T (CFSG.Quasithin.KGC31.M24.conjAll (candT 18) u5T) (frameVs 18) (frameCands fr2W) = true := KernelKGC31M24.cert7216

end Certificates
