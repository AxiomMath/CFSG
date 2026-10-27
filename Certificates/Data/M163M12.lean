module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163

open CFSG.Sporadic.Schreier CFSG.ClassicalInvolution

@[expose] def m12SqRoots1 : List (Equiv.Perm (Fin 12)) :=
  (enumerationTab m12CentQ1).filter fun x => decide (x * x = m12Rep1)

@[expose] def m12QuatCheck : Bool :=
  (enumerationTab m12CentQ1).all fun g =>
    (!decide (g * g = 1) && !decide (g * g * g = 1)) || decide (g = 1) || decide (g = m12Rep1) ||
      m12SqRoots1.all fun x => m12SqRoots1.all fun y =>
        !(decide (g * x = x * g) && decide (g * y = y * g)) || decide (x * y = y * x)

@[expose] def m12NoRoot2Check : Bool :=
  (enumerationTab m12CentQ2).all fun x => !decide (x * x = m12Rep2)

end CFSG.ClassicalInvolution.Q3.TL4.MF163
