module

public import Certificates.Data.Kernel.Misc.E6Std

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def bN (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

@[expose] noncomputable def letLB (codes bits : Nat) (l : Nat × Bool × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun j p => Prod.rec (motive := fun _ => Nat)
    (fun c₀ c₁ => rootB codes bits (Nat.add 6 j) (bN c₀) (bN c₁)) p) l

@[expose] noncomputable def twLB (codes bits : Nat) (gam : List Nat) (l : Nat × Bool × Bool) :
    Nat :=
  Prod.rec (motive := fun _ => Nat) (fun j p => Prod.rec (motive := fun _ => Nat)
    (fun c₀ c₁ => rootB codes bits (Nat.add 6 (nthV gam j))
      (bN (Bool.rec (motive := fun _ => Bool) c₁ (Bool.rec (motive := fun _ => Bool) true false c₁)
        c₀)) (bN c₁)) p) l

@[expose] noncomputable def wordLB (codes bits : Nat) (w : List (Nat × Bool × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (mulB acc (letLB codes bits l))) w oneB

@[expose] noncomputable def wordTB (codes bits : Nat) (gam : List Nat)
    (w : List (Nat × Bool × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (mulB acc (twLB codes bits gam l))) w oneB

@[expose] noncomputable def ltW (w : List (Nat × Bool × Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun j _ => Nat.blt j 72) l) ih) w

@[expose] noncomputable def colB (col : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => letN acc fun acc => blowCol l (col l) acc) (nat_lit 78)

@[expose] noncomputable def diagColK (es : List Nat) (l : Nat) : Nat :=
  letN (Nat.mod (nthV es l) 3) fun e =>
    Nat.lor (Nat.mul (Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq e 1)) (Nat.shiftLeft 1 l))
      (Nat.shiftLeft (Nat.mul (Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq e 0))
        (Nat.shiftLeft 1 l)) 78)

@[expose] noncomputable def diagB (es : List Nat) : Nat := colB (diagColK es)

@[expose] noncomputable def psiB (E ns : List Nat) : Nat :=
  mulB (mulB (mulB (mulB (powB (nthV E 0) (nthV ns 0)) (powB (nthV E 1) (nthV ns 1)))
    (powB (nthV E 2) (nthV ns 2))) (powB (nthV E 3) (nthV ns 3))) (powB (nthV E 4) (nthV ns 4))

end CFSG.KC.Misc.E6Std

end
