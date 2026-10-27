module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.LQT.PcW

open CFSG.KC.Enum

@[expose] noncomputable def pcS (n w m p q : Nat) : Nat :=
  strictN p (fun p => strictN q (fun q => pcomp n w m p q))

@[expose] noncomputable def wordPB (n w m : Nat) (L : Nat → Nat) (ws : List Nat) (b : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) b (fun l _ ih => pcS n w m (L l) ih) ws

@[expose] noncomputable def powS (n w m idn p k : Nat) : Nat :=
  strictN p (fun p => Nat.rec (motive := fun _ => Nat) idn (fun _ ih => pcS n w m p ih) k)

@[expose] noncomputable def qtW (n w m idn : Nat) (L : Nat → Nat) (ws : List Nat) (k : Nat) :
    Nat :=
  powS n w m idn (wordPB n w m L ws idn) k

@[expose] noncomputable def commS (n w m a b c d : Nat) : Nat :=
  pcS n w m (pcS n w m (pcS n w m a b) c) d

@[expose] noncomputable def rijS (n w m idn t₁ t₂ i j : Nat) : Nat :=
  pcS n w m (powS n w m idn t₁ i) (powS n w m idn t₂ j)

@[expose] noncomputable def neB (a b : Nat) : Bool := bIf(Nat.beq a b, false, true)

@[expose] noncomputable def memK (v : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq v a, true, ih)) l

@[expose] noncomputable def distF (l acc : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih acc => strictB x (fun v => bAnd(bIf(memK v acc, false, true), ih (List.cons v acc))))
    l acc

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def sortK (l : List Nat) (lb : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih lb => bAnd(Nat.ble lb a, ih (Nat.succ a))) l lb

@[expose] noncomputable def imgsK (w m c : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.cons (pg w m c x) ih) l

@[expose] noncomputable def labK (n w m c : Nat) (x : List Nat) : Bool :=
  bAnd(sortK x (nat_lit 0), bAnd(allL x (fun p => bAnd(Nat.blt p n, memK (pg w m c p) x)),
    distF (imgsK w m c x) []))

@[expose] noncomputable def labsK (n w m c : Nat) (xs : List (List Nat)) : Bool :=
  strictB c (fun c => allL xs (fun x => labK n w m c x))

end CFSG.KC.LQT.PcW

end
