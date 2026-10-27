module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.GH74.KGroups.PermCheck

public section

namespace Certificates.TL4MF163U3Inv

open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def centInvAt (LN : List M) (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)) ||
      (memB LN a && memB LN b) ||
      !(C.all fun x => !decide (x ^ 3 = 1) || decide (x * a = a * x ∧ x * b = b * x)) ||
      C.all fun c => !decide (c * c = 1 ∧ c * a = a * c ∧ c * b = b * c) || decide (c = 1) ||
        decide (c = t)

@[expose] def centInvCheck (LN L reps : List M) : Bool :=
  reps.all fun t => centInvAt LN t (centB L t)

@[expose] def u33CentInvCk (_ : Unit) : Bool :=
  centInvCheck (elemsT U33.QP) (elemsT U33.QA) (pickReps (elemsT U33.QA))

end Certificates.TL4MF163U3Inv
