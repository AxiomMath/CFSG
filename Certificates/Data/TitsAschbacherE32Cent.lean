module

public import Certificates.Data.TitsAschbacherE32

public section

namespace Certificates.TitsAschbacherE32

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott
  Certificates.TitsAschbacherSecFour

@[expose] def commF (a : Array ℕ) : Bool := fIdx.all fun i => commA a (vA i)

@[expose] def centFCheck (_ : Unit) : Bool :=
  let F := fArrs ()
  all5 1755 titsHLevels fun h =>
    (!commF h || F.any (eqA 1755 h)) && !commF (compA 1755 h CFSG.Quasithin.titsPiArr)

end Certificates.TitsAschbacherE32
