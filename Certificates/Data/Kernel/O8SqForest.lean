module

public import Certificates.Data.Kernel.PCent

public section

namespace CFSG.KC.O8Sq

open CFSG.KC.Enum (pcomp allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.PCent

@[expose] def recF (ACT : Nat → Nat → Nat) (ngen N nr : Nat) (RT : Nat → Nat) (r q : Rec) :
    Bool :=
  (Nat.beq r.2.1 (nat_lit 0) && Nat.blt r.2.2.1 nr && Nat.beq r.1 (RT r.2.2.1)) ||
    (Nat.blt r.2.2.2 N && Nat.blt r.2.2.1 ngen && Nat.blt q.2.1 r.2.1 &&
      Nat.beq r.1 (ACT r.2.2.1 q.1))

@[expose] noncomputable def walkF (ACT : Nat → Nat → Nat) (ngen N nr : Nat) (RT : Nat → Nat)
    (T : PTree Rec) : List Rec → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih lo => Nat.ble lo r.1 && recF ACT ngen N nr RT r (getT T r.2.2.2) &&
      ih (Nat.add r.1 (nat_lit 1)))

@[expose] noncomputable def forestK (n w : Nat) (G GI : Nat → Nat) (ngen : Nat) (RT : Nat → Nat)
    (nr : Nat) (R : List Rec) : Bool :=
  allN ngen (fun k => Nat.beq (GI k) (pinvS n w (mask w) (G k))) &&
    walkF (conjI n w G GI) ngen R.length nr RT (treeOf R) R (nat_lit 0)

@[expose] noncomputable def cpathK (n w : Nat) (G : Nat → Nat) (x : Nat) (ks : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k _ ih y => ih (conjI n w G G k y)) ks x

end CFSG.KC.O8Sq

end
