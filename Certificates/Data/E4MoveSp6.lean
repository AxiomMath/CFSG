module

public import Certificates.Data.E4QuatSp6Check
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.ClassicalInvolution

@[expose] def moveElems (_ : Unit) : List (Equiv.Perm (Fin 36)) := enumerationTab sp6CentQ2

@[expose] def moveInvs (L : List (Equiv.Perm (Fin 36))) : List (Equiv.Perm (Fin 36)) :=
  let r := tab sp6Rep2
  let ρ := rho ()
  let j := jay ()
  L.filter fun a => decide (a * a = 1 ∧ a ≠ 1 ∧ a ≠ r ∧ a * ρ = ρ * a ∧ a * j = j * a)

@[expose] def moveThrees (L : List (Equiv.Perm (Fin 36))) : List (Equiv.Perm (Fin 36)) :=
  L.filter fun c => decide (c * c * c = 1)

@[expose] def moveCheck (_ : Unit) : Bool :=
  let L := moveElems ()
  let T := moveThrees L
  (moveInvs L).all fun a => T.any fun c => decide (c * a ≠ a * c)

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
