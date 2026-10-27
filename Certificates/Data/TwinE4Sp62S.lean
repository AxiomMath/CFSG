module

public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.Sp62S

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier

@[expose] def sqRoots (r : Equiv.Perm (Fin 36)) (E : List (Equiv.Perm (Fin 36))) :
    List (Equiv.Perm (Fin 36)) :=
  (E.filter fun x => decide (x * x = r)).map tab

@[expose] def sqStep (S : List (Equiv.Perm (Fin 36))) (s : Equiv.Perm (Fin 36)) : Bool :=
  S.all (fun x => decide (x * s = s * x)) ||
    let X := S.filter fun x => decide (x * s = s * x)
    X.all fun x => X.all fun y => !decide (y * x * y⁻¹ = x⁻¹)

@[expose] def sqCheck (r : Equiv.Perm (Fin 36)) (E : List (Equiv.Perm (Fin 36))) : Bool :=
  let S := sqRoots r E
  S.isEmpty || E.all fun s => !decide (s * s = 1) || sqStep S (tab s)

@[expose] def sPropCheck (_ : Unit) : Bool :=
  sqCheck (tab sp6Rep1) (enumeration sp6CentQ1) && sqCheck (tab sp6Rep2) (enumeration sp6CentQ2) &&
    sqCheck (tab sp6Rep3) (enumeration sp6CentQ3) && sqCheck (tab sp6Rep4) (enumeration sp6CentQ4)

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.Sp62S
