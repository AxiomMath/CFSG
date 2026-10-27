module

public import Certificates.Data.E4QuatO8Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4A

@[expose] def threeCheck (_ : Unit) : Bool :=
  let L := L0A ()
  let u := u0A ()
  let v := v0A ()
  let a := (rootA ()).getD 0 (idA 360)
  let b := (rootA ()).getD 4 (idA 360)
  let c := (rootA ()).getD 6 (idA 360)
  edgeCheckA 360 L u v c && !normsA 360 L u v (compA 360 (invCand 360 a) c) &&
    !normsA 360 L u v (compA 360 (invCand 360 b) c)

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
