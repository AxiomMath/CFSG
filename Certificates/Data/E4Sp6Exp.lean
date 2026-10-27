module

public import Certificates.Data.E4QuatSp6Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def centSqStep (i j i1 j1 : Equiv.Perm (Fin 36)) (g : Equiv.Perm (Fin 36)) : Bool :=
  decide (g * i = i * g) && decide (g * j = j * g) && decide (g * i1 = i1 * g) &&
    decide (g * j1 = j1 * g) && !decide (g * g = 1)

@[expose] def centSqCheck (_ : Unit) : Bool :=
  let t := twin ()
  let i := rho ()
  let j := jay ()
  let i1 := tab (t * i * t⁻¹)
  let j1 := tab (t * j * t⁻¹)
  (enumeration sp6CentQ2).all fun g => !centSqStep i j i1 j1 (tab g)

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
