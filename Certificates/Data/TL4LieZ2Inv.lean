module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.GH74.KGroups.M11Inputs
public import CFSG.GH74.KGroups.PermCheck

public section

namespace Certificates.TL4LieZ2Inv

open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def q8InvAt (t : M) (CP CA : List M) : Bool :=
  (CP.filter fun a => decide (a * a = t)).all fun a =>
    (CP.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
        CA.all fun c => !decide (c * c = 1 ∧ c * a = a * c ∧ c * b = b * c) ||
          decide (c = 1) || decide (c = t)

@[expose] def q8InvCheck (LP LA reps : List M) : Bool :=
  coverB reps LP && reps.all fun t => q8InvAt t (centB LP t) (centB LA t)

@[expose] def l33Q8InvCk (_ : Unit := ()) : Bool :=
  let LP := elemsT L33.QP
  q8InvCheck LP (elemsT L33.QA) (pickReps LP)

@[expose] def m11Q8InvCk (_ : Unit := ()) : Bool :=
  let L := elemsT M11.Q
  q8InvCheck L L (pickReps L)

end Certificates.TL4LieZ2Inv
