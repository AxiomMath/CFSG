module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.SlpRel

open CFSG.KC.Enum

variable {α : Type}

@[expose] noncomputable def wordS (frc : α → (α → Bool) → Bool) (mul : α → α → α) (one : α)
    (R : List α) (w : List Nat) (acc : α) (k : α → Bool) : Bool :=
  List.rec (motive := fun _ => α → Bool) k
    (fun l _ ih acc => frc (mul acc (List.getD R (Nat.sub l (nat_lit 1)) one)) ih) w acc

@[expose] noncomputable def slpS (frc : α → (α → Bool) → Bool) (mul : α → α → α) (one : α)
    (prog : List (List Nat)) (R : List α) (K : List α → Bool) : Bool :=
  List.rec (motive := fun _ => List α → Bool) K
    (fun w _ ih R => wordS frc mul one R w one fun x => ih (List.append R [x])) prog R

@[expose] noncomputable def pairsS (frc : α → (α → Bool) → Bool) (mul : α → α → α) (one : α)
    (eq : α → α → Bool) (R : List α) (ps : List (List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => wordS frc mul one R p.1 one fun a => wordS frc mul one R p.2 one fun b =>
      bAnd(eq a b, ih)) ps

@[expose] noncomputable def nesS (nz : α → Bool) (one : α) (R : List α) (ne : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(nz (List.getD R (Nat.sub l (nat_lit 1)) one), ih)) ne

@[expose] noncomputable def slpRelK (frc : α → (α → Bool) → Bool) (mul : α → α → α) (one : α)
    (eq : α → α → Bool) (nz : α → Bool) (init : List α) (prog : List (List Nat))
    (ps : List (List Nat × List Nat)) (ne : List Nat) : Bool :=
  slpS frc mul one prog init fun R => bAnd(pairsS frc mul one eq R ps, nesS nz one R ne)

end CFSG.KC.SlpRel

end
