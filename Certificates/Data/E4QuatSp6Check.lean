module

public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
public import Certificates.Data.E4QuatCheck
public import Certificates.Data.E4QuatSp6

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def tabs (l : List (Equiv.Perm (Fin 36))) : List (Equiv.Perm (Fin 36)) := l.map tab

@[expose] def rho (_ : Unit) : Equiv.Perm (Fin 36) := tab (evalCodes sp6CentGens2 [1, 1, 1])

@[expose] def jay (_ : Unit) : Equiv.Perm (Fin 36) :=
  tab (evalCodes sp6CentGens2 [2, 1, 3, 3, 1, 1, 2])

@[expose] def L0 (_ : Unit) : List (Equiv.Perm (Fin 36)) := q8Elems (tab sp6Rep2) (rho ()) (jay ())

@[expose] def ws (_ : Unit) : List (Equiv.Perm (Fin 36)) :=
  memberWords.map fun w => tab (evalCodes sp6Gens w)

@[expose] def twin (_ : Unit) : Equiv.Perm (Fin 36) := (ws ()).getD 11 1

@[expose] def L1 (_ : Unit) : List (Equiv.Perm (Fin 36)) :=
  (L0 ()).map fun y => twin () * y * (twin ())⁻¹

@[expose] def U (_ : Unit) : List (Equiv.Perm (Fin 36)) := (L0 ()).drop 2

@[expose] def W (_ : Unit) : List (Equiv.Perm (Fin 36)) := [tab (sp6CentGens2.getD 0 1)]

@[expose] def check (_ : Unit) : Bool :=
  decide (rho () * rho () = tab sp6Rep2) && closedL (L0 ()) (rho ()) (jay ()) &&
    identCheck (tab sp6Rep1) (tabs sp6FourReps1) (enumeration sp6CentQ1) [] [] [] &&
    identCheck (tab sp6Rep2) (tabs sp6FourReps2) (enumeration sp6CentQ2) (W ()) (L0 ()) (L1 ()) &&
    identCheck (tab sp6Rep3) (tabs sp6FourReps3) (enumeration sp6CentQ3) [] [] [] &&
    identCheck (tab sp6Rep4) (tabs sp6FourReps4) (enumeration sp6CentQ4) [] [] [] &&
    memberCheck sp6Gens (L0 ()) (rho ()) (jay ()) (ws ()) memberSigma &&
    treeCheck (L0 ()) (U ()) (rho ()) (jay ()) (ws ()) memberTree &&
    nbrCheck (L0 ()) (rho ()) (jay ()) (ws ()) [0, 11] &&
    edgeCheck (L0 ()) (rho ()) (jay ()) (twin ())

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
