module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.Leech

open CFSG.KLie.CT

@[expose] noncomputable def getK (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) l

@[expose] noncomputable def memL (l : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (Nat.beq a x) ih) l

@[expose] noncomputable def treeAt (P : Nat → Bool) (n : Nat) (V PA LV : Nat → Nat) (i : Nat) :
    Bool :=
  orB (Nat.beq i (nat_lit 0)) (andB (Nat.blt (PA i) n)
    (andB (Nat.beq (Nat.succ (LV (PA i))) (LV i)) (P (Nat.xor (V i) (V (PA i))))))

@[expose] noncomputable def longAt (P : Nat → Bool) (n w : Nat) (V PA LV : Nat → Nat) (i : Nat) :
    Bool :=
  orB (Nat.beq i (nat_lit 0)) (andB (Nat.blt (PA i) n)
    (andB (Nat.beq (Nat.succ (LV (PA i))) (LV i)) (andB (P (Nat.xor (V i) (V (PA i))))
      (notB (Nat.beq (Nat.xor (V i) (V (PA i))) w)))))

@[expose] noncomputable def sortedAt (n : Nat) (V : Nat → Nat) (i : Nat) : Bool :=
  orB (Nat.beq (Nat.succ i) n) (Nat.blt (V i) (V (Nat.succ i)))

@[expose] noncomputable def nbrAt (P : Nat → Bool) (V : Nat → Nat) (i : Nat) : Bool :=
  andB (P (V i)) (P (Nat.xor (V i) (nat_lit 12288)))

@[expose] noncomputable def muVsAt (P : Nat → Bool) (b : Nat) (V : Nat → Nat) (i : Nat) : Bool :=
  andB (P (V i)) (andB (P (Nat.xor (V i) (nat_lit 12288))) (P (Nat.xor (V i) b)))

@[expose] noncomputable def muNbrAt (P : Nat → Bool) (b : Nat) (NB : Nat → Nat) (W : List Nat)
    (i : Nat) : Bool :=
  orB (notB (P (Nat.xor (NB i) b))) (memL W (NB i))

@[expose] noncomputable def allFrom (o m : Nat) (f : Nat → Bool) : Bool :=
  allN m fun j => f (Nat.add o j)

end CFSG.KC.Leech

end
