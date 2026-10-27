module

public import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.Kernel.F2Word
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs

public section

namespace CFSG.KC.OpsK

open CFSG.KC.Loop CFSG.SectionRank.Native CFSG.Sporadic.GLQ

@[expose] noncomputable def forceB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def powN {V : Type} (O : Ops Nat V) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => O.one)
    (fun _ ih X e => nIf(Nat.beq e 0, O.one, nIf(Nat.beq e 1, X,
      strictN (O.mul X X) fun X2 => strictN (ih X2 (Nat.div e 2)) fun Y =>
        nIf(Nat.beq (Nat.mod e 2) 1, O.mul X Y, Y)))) f

@[expose] noncomputable def stepK {V : Type} (O : Ops Nat V) (R : Array (Nat × Nat))
    (k : Array (Nat × Nat) → Bool) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool)
    (fun i j t => forceB (O.mul R[i]!.1 R[j]!.1) fun a => forceB (O.mul R[j]!.2 R[i]!.2) fun b =>
      k (R.setIfInBounds t (a, b)))
    (fun i t => k (R.setIfInBounds t (R[i]!.2, R[i]!.1)))
    (fun e i t => forceB (powN O (Nat.succ e) R[i]!.1 e) fun a =>
      forceB (powN O (Nat.succ e) R[i]!.2 e) fun b => k (R.setIfInBounds t (a, b)))
    ins

@[expose] noncomputable def runK {V : Type} (O : Ops Nat V) (prog : List Instr) :
    Array (Nat × Nat) → (Array (Nat × Nat) → Bool) → Bool :=
  List.rec (motive := fun _ => Array (Nat × Nat) → (Array (Nat × Nat) → Bool) → Bool)
    (fun R k => k R) (fun ins _ ih R k => stepK O R (fun R' => ih R' k) ins) prog

@[expose] noncomputable def forceL (xs : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => forceB x fun x' => ih fun l => k (x' :: l)) xs k

@[expose] noncomputable def opsF2K (d : Nat) : Ops Nat Nat where
  decode _ := 0
  mul := CFSG.KC.F2W.mulW d
  one := CFSG.KC.M1F2.idF d
  eq X Y := Nat.beq (Nat.mod X (Nat.shiftLeft 1 (Nat.mul d d)))
    (Nat.mod Y (Nat.shiftLeft 1 (Nat.mul d d)))
  vmul v X := CFSG.KC.M1F2.vmF d X v
  unit k := Nat.shiftLeft 1 k
  vne u w := Bool.not (Nat.beq (Nat.mod u (Nat.shiftLeft 1 d)) (Nat.mod w (Nat.shiftLeft 1 d)))

end CFSG.KC.OpsK

end
