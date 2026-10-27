module

public import Certificates.Data.Kernel.YModel.Model
public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KC.B4A

open CFSG.KC CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] def dWL : List Nat := (List.replicate 9 [0, 1, 2, 3, 8, 9, 5]).flatten

@[expose] def dpW (τ : List Nat) : List Nat := τ ++ dWL ++ τ.reverse

@[expose] noncomputable def wOfL (l : List Nat) : Nat :=
  wMk l.length (List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ acc => Nat.add c (Nat.mul (nat_lit 16) acc)) l)

@[expose] noncomputable def allP : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 31671)) (nat_lit 1)

section
variable (Nf : Nat → Nat)

@[expose] noncomputable def apP (P : Nat) (w : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (netApply (nat_lit 15) (wid (nat_lit 15)) (repU (wid (nat_lit 15)) P) (Nf c) x) ih)
    w X

@[expose] noncomputable def sideOf (Y p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) Y (Nat.xor allP Y) (bitB Y p)

@[expose] noncomputable def hubE (Y F0 p : Nat) (τ : List Nat) : Nat :=
  Nat.land (apP Nf (nat_lit 1) (dpW τ) (sideOf Y p)) (Nat.xor allP (apP Nf (nat_lit 1) τ.reverse F0))

@[expose] noncomputable def nodeX (Y F0 : Nat) (H : List (Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) allP
    (fun h _ X => Nat.land X (Nat.xor allP (hubE Nf Y F0 h.1 h.2))) H

@[expose] noncomputable def hubOK (p : Nat) (τ : List Nat) : Bool :=
  Nat.beq (apP Nf (nat_lit 1) τ.reverse (nat_lit 1)) (Nat.shiftLeft (nat_lit 1) p)

end

@[expose] noncomputable def planeAt (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul (wid (nat_lit 15)) i)) (ones (wid (nat_lit 15)))

@[expose] noncomputable def permPlanes (X : Nat) (σ : List Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun s _ ih i => Nat.lor (Nat.shiftLeft (planeAt X s) (Nat.mul (wid (nat_lit 15)) i)) (ih (Nat.succ i)))
    σ) (nat_lit 0)

@[expose] noncomputable def ptPlanes (A : List Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (wid (nat_lit 15)) i) a)) (ih (Nat.succ i)))
    A) (nat_lit 0)

end CFSG.KC.B4A

end
