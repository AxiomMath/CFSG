module

public import Certificates.Data.E4QuatO8Check

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0Check

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Q3.TL4.E4O8

@[expose] def om0Comm (_ : Unit := ()) : Bool :=
  [0, 1, 2, 4, 5, 6, 7].all fun l =>
    eqA 360 (compA 360 genArrs[l]! (xA 0)) (compA 360 (xA 0) genArrs[l]!)

@[expose] def om0Prod (_ : Unit := ()) : Bool :=
  eqA 360 (conjArr genArrs[3]! (xA 0))
    (compA 360 (compA 360 (compA 360 (conjArr genArrs[0]! (v0A ())) (conjArr genArrs[2]! (v0A ())))
      (conjArr genArrs[4]! (v0A ()))) (conjArr genArrs[6]! (compA 360 (v0A ()) (xA 0))))

@[expose] def om0GenCheck (_ : Unit := ()) : Bool := om0Comm () && om0Prod ()

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0Check
