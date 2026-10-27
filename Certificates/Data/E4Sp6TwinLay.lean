module

public import Certificates.Data.E4QuatSp6Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def commAll (g : Equiv.Perm (Fin 36)) (l : List (Equiv.Perm (Fin 36))) : Bool :=
  l.all fun x => decide (g * x = x * g)

@[expose] def memberElems (L : List (Equiv.Perm (Fin 36))) (w : Equiv.Perm (Fin 36)) :
    List (Equiv.Perm (Fin 36)) :=
  L.map fun q => tab (w * q * w⁻¹)

@[expose] def ordThree (c : Equiv.Perm (Fin 36)) : Bool :=
  !decide (c = 1) && decide (c * c * c = 1)

@[expose] def twinLayCheck (_ : Unit) : Bool :=
  let L := L0 ()
  let L' := L1 ()
  let W := ws ()
  let C8 := ((enumeration sp6CentQ2).map tab).filter fun g => commAll g L && commAll g L'
  let lay := C8.filter fun c => !decide (c = 1) &&
    !((List.range W.length).all fun k => k == 0 || k == 11 || !commAll c (memberElems L (W.getD k 1)))
  lay.all fun a => lay.all fun b => decide (a = b) ||
    (List.range W.length).any fun k =>
      commAll a (memberElems L (W.getD k 1)) &&
        (memberElems L (W.getD k 1)).any fun z => ordThree (z * b * z⁻¹ * b⁻¹)

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
