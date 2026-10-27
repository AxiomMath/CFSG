
module

public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public import CFSG.Quasithin.H13.A5M12SylBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H.Mathieu

@[expose] def quadBasisOK {P : Type*} (n : ℕ) (act : P → ℕ → ℕ) (l : List P) : Bool :=
  l.all fun s => l.all fun t => (List.range n).all fun j =>
    act s (act t (2 ^ j) ^^^ 2 ^ j) == (act t (2 ^ j) ^^^ 2 ^ j)

@[expose] def predQ {P : Type*} (n : ℕ) (act : P → ℕ → ℕ) (strict : Bool) (l : List P) : Bool :=
  l.isEmpty || !quadBasisOK n act l ||
    (if strict then decide (2 * l.length < n - Nat.log 2 (fixMasks n act l).length)
    else decide (2 * l.length ≤ n - Nat.log 2 (fixMasks n act l).length))

@[expose] def actC24s2 (p : T24s2.Elem) (m : ℕ) : ℕ := actM (matsC24[p.idx]!) m

@[expose] def actC22s2 (p : T22s2.Elem) (m : ℕ) : ℕ := actM (matsC22[p.idx]!) m

end CFSG.Quasithin.B45Mat
