module

public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeTorusInputs
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
import Certificates.Kernel.StdOdd.SylowThreeTorus

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley in
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel in
open CFSG.Monster.B.Classical.E6Adjoint in
open CFSG.Monster.Existence.StdOdd.P5 (E5 rk) in
theorem certificate6039 : (CertNative.fixedOK bracketCodes formBits gamTable
      ((List.range 5).map eWord) = true)
    ∧ (CertNative.torusOK bracketCodes formBits ((List.range 5).map hWord)
      torusExps = true)
    ∧ (∀ j < 5, ∀ l ∈ hWord j, l.1 < 72)
    ∧ (∀ j < 5, ∀ l ∈ eWord j, l.1 < 72)
    ∧ (∀ v : E5, (∀ p : Fin 78, exN v p % 3 = 0) → v = 0)
    ∧ (∀ v : E5,
      (Finset.univ.filter fun p : Fin 78 => exN v p % 3 ≠ 0).card + rk v = 72) := CFSG.KD.StdOdd.SylowThreeTorus.facts

end Certificates
