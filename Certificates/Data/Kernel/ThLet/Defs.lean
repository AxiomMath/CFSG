module

public import Certificates.Data.Kernel.ThCent.Pin

public section

namespace CFSG.KC.ThLet

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.SectionRank.Native

@[expose] noncomputable def runK (c rm ONE : Nat) (prog : List Op) :
    (Nat → Nat) → ((Nat → Nat) → Bool) → Bool :=
  List.rec (motive := fun _ => (Nat → Nat) → ((Nat → Nat) → Bool) → Bool) (fun R k => k R)
    (fun op _ ih R k => Op.rec (motive := fun _ => Bool)
      (fun i j t => strictF (mulB c rm (R i) (R j)) fun v => ih (updN R t v) k)
      (fun e i t => strictF (powB c rm ONE (R i) e (nat_lit 6)) fun v => ih (updN R t v) k) op)
    prog

@[expose] noncomputable def letK (E Ei : Nat → Nat) (x : Fin 6 × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Ei x.1.val) (E x.1.val) x.2

@[expose] noncomputable def relFrom (c rm : Nat) (E Ei : Nat → Nat) (r : List (Fin 6 × Bool)) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => strictF (mulB c rm acc (letK E Ei x)) ih) r

@[expose] noncomputable def relsOK (c rm ONE : Nat) (E Ei : Nat → Nat)
    (ws : List (List (Fin 6 × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (relFrom c rm E Ei r ONE) ONE) ih) ws

@[expose] noncomputable def pairsOK (c rm ONE S : Nat) (E Ei : Nat → Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (andB (Nat.beq (mulB c rm (E k) (Ei k)) ONE)
      (Nat.beq (mulB c rm S (E k)) (mulB c rm (E k) S))) ih) n

end CFSG.KC.ThLet

end
