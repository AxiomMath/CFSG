module

public import CFSG.Quasithin.H13.A5M12SylBase
public import CFSG.Quasithin.H13.A5M12SylInputs
public import CFSG.Quasithin.Background.HMathieuPred
public import Certificates.Certificate7112
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12

@[expose] def predR {P : Type*} (n : ℕ) (act : P → ℕ → ℕ) (l : List P) : Bool :=
  l.isEmpty || decide (2 * l.length ≤ n - Nat.log 2 (fixMasks n act l).length)

@[expose] def inv12s2F [Fact (T12s2.check = true)] : List T12s2.Elem := T12s2.invols

@[expose] def pos12s2F [Fact (T12s2.check = true)] (x : T12s2.Elem) : ℕ :=
  (T12s2.posArr inv12s2F)[x.idx]!

end CFSG.Quasithin.B45Mat
