module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Tits8074

@[expose] noncomputable def ap (L : Nat → Nat) (c p : Nat) : Nat := fld(L c, Nat.mul 11 p, 2047)

@[expose] noncomputable def ev (L : Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun c _ ih => ap L c ih) w

@[expose] noncomputable def evI (L : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun c _ ih p => ih (ap L (Nat.xor c 1) p)) w

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) l

@[expose] noncomputable def anyL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(f a, true, ih)) l

@[expose] noncomputable def bs : List Nat := [0, 3, 1, 5, 6, 12, 24]

@[expose] noncomputable def codes : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] noncomputable def gx (L : Nat → Nat) (z : Nat) (t : List Nat) (p : Nat) : Nat :=
  ev L t (ap L z (evI L t (ap L 2 p)))

@[expose] noncomputable def iter (L : Nat → Nat) (z : Nat) (t : List Nat) (m p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => gx L z t ih) m

@[expose] noncomputable def walk (L : Nat → Nat) (z : Nat) (E : List (List Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih q => bAnd(Nat.beq (ev L e.1 0) q,
      bAnd(bIf(Nat.beq e.2 2047, true, bAnd(Nat.blt e.2 1755,
        bIf(Nat.beq (iter L z e.1 13 e.2) e.2, false, true))), ih (Nat.succ q)))) E

@[expose] noncomputable def nGood (E : List (List Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => nIf(Nat.beq e.2 2047, Nat.succ ih, ih)) E

@[expose] noncomputable def commF (f g : Nat → Nat) : Bool :=
  allL bs fun p => Nat.beq (f (g p)) (g (f p))

@[expose] noncomputable def commB (L : Nat → Nat) (c d : Nat) : Bool := commF (ap L c) (ap L d)

@[expose] noncomputable def fixes (L : Nat → Nat) (pre : List Nat) (c : Nat) : Bool :=
  allL pre fun p => Nat.beq (ap L c p) p

@[expose] noncomputable def cenZ (L : Nat → Nat) (z : Nat) : Bool :=
  allL codes fun c => bIf(fixes L [0] c, commB L z c, true)

@[expose] noncomputable def conjB (L : Nat → Nat) (a : Nat) (t : List Nat) (z : Nat) : Bool :=
  allL bs fun p => Nat.beq (ap L a p) (ev L t (ap L z (evI L t p)))

@[expose] noncomputable def orbK (L : Nat → Nat) (R : List (List Nat)) (pre : List Nat) (b : Nat) :
    Bool :=
  bAnd(allL R fun u => allL u fun c => fixes L pre c,
    allL R fun u => allL codes fun c => bIf(fixes L pre c,
      anyL R fun v => Nat.beq (ev L v b) (ap L c (ev L u b)), true))

@[expose] noncomputable def pairK (L : Nat → Nat) (s : Nat) : Bool :=
  bAnd(allL codes fun c => bIf(fixes L [0, 3] c, Nat.beq (ap L c 4) 4, true),
    bAnd(Nat.beq (ap L s 0) 0, bAnd(Nat.beq (ap L s 3) 4, Nat.beq (ap L s 4) 3)))

@[expose] noncomputable def zOne (L : Nat → Nat) (z s : Nat) (f : Nat → Nat) : Bool :=
  bIf(commF f (ap L s),
    bIf(allL codes fun c => bIf(fixes L [0, 3] c, commF f (ap L c), true),
      bIf(allL bs fun p => Nat.beq (f p) p, true, allL bs fun p => Nat.beq (f p) (ap L z p)),
      true),
    true)

@[expose] noncomputable def zsK (L : Nat → Nat) (z s : Nat) (e : Bool)
    (R₂ R₃ R₄ R₅ R₆ : List (List Nat)) : Bool :=
  allL R₂ fun u₂ => allL R₃ fun u₃ => allL R₄ fun u₄ => allL R₅ fun u₅ => allL R₆ fun u₆ =>
    zOne L z s fun p =>
      (fun y => nIf(e, ap L s y, y)) (ev L u₂ (ev L u₃ (ev L u₄ (ev L u₅ (ev L u₆ p)))))

end CFSG.KC.Tits8074

end
