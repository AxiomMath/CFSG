module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck

public section

namespace Certificates.PSp43NoQ8

open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups
open CFSG.ComponentClassification.CatFactsSmall

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def noQ8PairsB (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹))

@[expose] def noQ8Check (L reps : List M) : Bool :=
  reps.all fun t => noQ8PairsB t (centB L t)

@[expose] def chkP (_ : Unit) : Bool :=
  noQ8Check (elemsT PSp43.QP45) (pickReps (elemsT PSp43.QP45))

@[expose] def chkA (_ : Unit) : Bool :=
  noQ8Check (elemsT PSp43.QA45) (pickReps (elemsT PSp43.QA45))

end Certificates.PSp43NoQ8
