module

public import Certificates.Data.Kernel.Tits8074

public section

namespace CFSG.KC.Tits8074

@[expose] noncomputable def pgf (P p : Nat) : Nat := fld(P, Nat.mul 11 p, 2047)

@[expose] noncomputable def genEq (L G : Nat → Nat) (W : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => bAnd(CFSG.KC.Loop.allBelow 1755 28 fun p => Nat.beq (pgf (G k) p) (ev L w p),
      ih (Nat.succ k))) W

@[expose] noncomputable def commG (L G : Nat → Nat) (n c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(commF (pgf (G k)) (ap L c), ih)) n

@[expose] noncomputable def conjK (L T : Nat → Nat) (W : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => bAnd(bIf(Nat.beq i 0, true,
      allL bs fun p => Nat.beq (ev L w (pgf (T i) p)) (ap L 2 (ev L w p))), ih (Nat.succ i))) W

end CFSG.KC.Tits8074

end
