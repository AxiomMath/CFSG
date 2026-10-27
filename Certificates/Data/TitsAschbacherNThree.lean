module

public import Certificates.Data.TitsAschbacherParrott

public section

namespace Certificates.TitsAschbacherNThree

open CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott

@[expose] def v3w2Arr (_ : Unit) : Array ℕ := compA 1755 (vA 3) w2Arr

@[expose] def s3Check (_ : Unit) : Bool :=
  eqA 1755 (compA 1755 (vA 3) (vA 3)) (idA 1755) && !eqA 1755 (v3w2Arr ()) (idA 1755) &&
    eqA 1755 (powA (v3w2Arr ()) 3) (idA 1755)

end Certificates.TitsAschbacherNThree
