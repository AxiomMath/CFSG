module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.SectionRank.Native

universe u

@[expose] noncomputable def strictF {α : Sort u} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letZ (A B Bi : Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun n => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) Bi B (Nat.beq n (nat_lit 2))) A (Nat.beq n (nat_lit 1)))
    (fun n => Bool.rec (motive := fun _ => Nat) Bi A (Nat.beq n (nat_lit 0))) l

@[expose] noncomputable def wordFrom (c rm A B Bi : Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictF (mulB c rm acc (letZ A B Bi l)) ih) w

@[expose] noncomputable def wordZ (c rm ONE A B Bi : Nat) (w : List Int) : Nat :=
  wordFrom c rm A B Bi w ONE

@[expose] noncomputable def updN (R : Nat → Nat) (k v : Nat) : Nat → Nat :=
  fun r => Bool.rec (motive := fun _ => Nat) (R r) v (Nat.beq r k)

@[expose] noncomputable def initPk (A B ONE : Nat) : Nat → Nat :=
  fun r => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) ONE B (Nat.beq r (nat_lit 1))) A (Nat.beq r (nat_lit 0))

@[expose] noncomputable def runPk (c rm ONE : Nat) (prog : List Op) : (Nat → Nat) → Nat → Nat :=
  List.rec (motive := fun _ => (Nat → Nat) → Nat → Nat) (fun R => R)
    (fun op _ ih R => Op.rec (motive := fun _ => Nat → Nat)
      (fun i j k => strictF (mulB c rm (R i) (R j)) fun v => ih (updN R k v))
      (fun e i k => strictF (powB c rm ONE (R i) e (nat_lit 6)) fun v => ih (updN R k v)) op) prog

@[expose] def powsOK (prog : List Op) : Bool :=
  prog.all fun
    | .mul _ _ _ => true
    | .pow e _ _ => Nat.blt e 64

end CFSG.KC.ThCent

end
