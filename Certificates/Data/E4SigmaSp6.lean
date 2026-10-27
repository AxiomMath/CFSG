module

public import Certificates.Data.E4QuatSp6Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def sigStep (i j i1 j1 : Equiv.Perm (Fin 36)) (L1 : List (Equiv.Perm (Fin 36)))
    (g : Equiv.Perm (Fin 36)) : Bool :=
  decide (g * g = 1) && decide (g * i = i * g) && decide (g * j = j * g) &&
    L1.any fun w => !decide (w * w = 1) && decide (g * i1 * g * w = w * i1) &&
      decide (g * j1 * g * w = w * j1)

@[expose] def sigCheck (_ : Unit) : Bool :=
  let t := twin ()
  let i := rho ()
  let j := jay ()
  let i1 := tab (t * i * t⁻¹)
  let j1 := tab (t * j * t⁻¹)
  let L1t := (L1 ()).map tab
  (enumeration sp6CentQ2).all fun g => !sigStep i j i1 j1 L1t (tab g)

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
