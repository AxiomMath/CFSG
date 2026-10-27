module

public import Certificates.Data.Kernel.SortTree
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.InvFam

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def actC (R I Ii : List Nat) (l X : Nat) : Nat :=
  mulW (nat_lit 24) (mulW (nat_lit 24) (getL (nat_lit 0) R (getL (nat_lit 0) I l)) X)
    (getL (nat_lit 0) R (getL (nat_lit 0) Ii l))

@[expose] noncomputable def actV (RT I : List Nat) (l v : Nat) : Nat :=
  vmF (nat_lit 24) (getL (nat_lit 0) RT (getL (nat_lit 0) I l)) v

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) L

@[expose] noncomputable def bndK (n : Nat) (L : List Nat) : Bool := allL L fun i => Nat.blt i n

@[expose] noncomputable def fixAllK (RT I vs : List Nat) : Bool :=
  allL I fun i => allL vs fun v => Nat.beq (vmF (nat_lit 24) (getL (nat_lit 0) RT i) v) v

@[expose] noncomputable def invPairsK (R I Ii : List Nat) : Bool :=
  andB (Nat.beq (lenL I) (lenL Ii)) (allN (lenL I) fun l =>
    Nat.beq (mulF (nat_lit 24) (getL (nat_lit 0) R (getL (nat_lit 0) I l))
      (getL (nat_lit 0) R (getL (nat_lit 0) Ii l))) (idF (nat_lit 24)))

@[expose] noncomputable def rootK (R r : List Nat) (s : Nat) : Bool :=
  andB (Nat.beq (lenL r) (nat_lit 3))
    (andB (Nat.beq (mulF (nat_lit 24) (getL (nat_lit 0) R (getL (nat_lit 0) r (nat_lit 0)))
      (getL (nat_lit 0) R (getL (nat_lit 0) r (nat_lit 1)))) (idF (nat_lit 24)))
    (Nat.beq (mulF (nat_lit 24) (mulF (nat_lit 24) (getL (nat_lit 0) R (getL (nat_lit 0) r (nat_lit 0)))
      (getL (nat_lit 0) R s)) (getL (nat_lit 0) R (getL (nat_lit 0) r (nat_lit 1))))
      (getL (nat_lit 0) R (getL (nat_lit 0) r (nat_lit 2)))))

@[expose] noncomputable def canonK (M : Nat) : Nat :=
  orN (nat_lit 24) fun i => Nat.shiftLeft (rowF (nat_lit 24) M i) (Nat.mul (nat_lit 24) i)

@[expose] noncomputable def stepsK (M : Nat) (j : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun C Rs => andB (Nat.beq (mulF (nat_lit 24) C M) (idF (nat_lit 24))) (Nat.beq C Rs))
    (fun _ ih C Rs => strictB (mulF (nat_lit 24) C M) fun N =>
      andB (notB (Nat.beq N (idF (nat_lit 24)))) (ih N Rs)) j

@[expose] noncomputable def chunksK (act : Nat → Nat → Nat) (ng root : Nat) (rec : Nat → Nat)
    (n wv wl wp B lo cnt : Nat) : Bool :=
  allN cnt fun j => CFSG.KC.SortTree.chunkOK act ng (fun _ => true) root rec n wv wl wp B (Nat.add lo j)

end CFSG.KC.InvFam

end
