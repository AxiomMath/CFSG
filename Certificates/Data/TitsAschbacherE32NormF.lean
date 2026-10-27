module

public import Certificates.Data.TitsAschbacherE32

public section

namespace Certificates.TitsAschbacherE32

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott
  Certificates.TitsAschbacherSecFour

@[expose] def memL (L : List (Array ℕ)) (a : Array ℕ) : Bool := L.any (eqA 1755 a)

@[expose] def interCount (L M : List (Array ℕ)) : ℕ := (L.filter (memL M)).length

@[expose] def e32NormCheck (_ : Unit) : Bool :=
  let E := eArrs ()
  let F := fArrs ()
  let X := xkSet E F (xkData.getD 4 (false, false, []))
  xkData.all (fun e =>
    !e.2.1 || (e.2.2 == [] && !e.1) || decide (interCount (xkSet E F e) F ≤ 8)) &&
    !memL E (vA 7) && memL X (vA 2) && decide (interCount X E ≤ 8) &&
    X.all (fun x => (List.range 5).all fun i =>
      memL E (compA 1755 (compA 1755 x (vA (8 + i))) x))

end Certificates.TitsAschbacherE32
