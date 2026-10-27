module

public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.HatHe

open CFSG.KC.Enum (pg strictB)
open CFSG.KC.Misc.Clos (treeAt closedAt sortAt)

@[expose] noncomputable def ap (P p : Nat) : Nat := pg 14 16383 P p

@[expose] noncomputable def actT (P t : Nat) : Nat :=
  Nat.lor (ap P (Nat.land t 16383))
  (Nat.lor (Nat.shiftLeft (ap P (fld(t, 14, 16383))) 14)
  (Nat.lor (Nat.shiftLeft (ap P (fld(t, 28, 16383))) 28)
  (Nat.lor (Nat.shiftLeft (ap P (fld(t, 42, 16383))) 42)
    (Nat.shiftLeft (ap P (Nat.shiftRight t 56)) 56))))

@[expose] noncomputable def actW (G : Nat → Nat) (w : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) t (fun l _ ih => actT (G l) ih) w

@[expose] noncomputable def apW (G : Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun l _ ih => ap (G l) ih) w

@[expose] noncomputable def sel9 (L0 L1 L2 L3 L4 L5 L6 L7 L8 k : Nat) : Nat :=
  nIf(Nat.beq k 0, L0, nIf(Nat.beq k 1, L1, nIf(Nat.beq k 2, L2, nIf(Nat.beq k 3, L3,
  nIf(Nat.beq k 4, L4, nIf(Nat.beq k 5, L5, nIf(Nat.beq k 6, L6, nIf(Nat.beq k 7, L7, L8))))))))

@[expose] noncomputable def with9 (F : Nat → Nat) (f : (Nat → Nat) → Bool) : Bool :=
  strictB (F 0) fun L0 => strictB (F 1) fun L1 => strictB (F 2) fun L2 =>
  strictB (F 3) fun L3 => strictB (F 4) fun L4 => strictB (F 5) fun L5 =>
  strictB (F 6) fun L6 => strictB (F 7) fun L7 => strictB (F 8) fun L8 =>
  f (sel9 L0 L1 L2 L3 L4 L5 L6 L7 L8)

@[expose] noncomputable def lsel (b : Bool) (x y : List Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) y x b

@[expose] noncomputable def B0 : Nat := 288243570828132352

@[expose] noncomputable def par (PA : Nat → Nat) (k : Nat) : Nat := Nat.land (PA k) 16777215

@[expose] noncomputable def lab (PA : Nat → Nat) (k : Nat) : Nat := Nat.shiftRight (PA k) 24

@[expose] noncomputable def trV (G : Nat → Nat) (W : Nat → List Nat) (PA : Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih k p => nIf(Nat.beq k 0, p, apW G (W (lab PA k)) (ih (par PA k) p))) f

@[expose] noncomputable def rootK (PA : Nat → Nat) (f : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k 0)
    (fun _ ih k => bIf(Nat.beq k 0, true, ih (par PA k))) f

@[expose] noncomputable def ncK (G : Nat → Nat) (W : Nat → List Nat) (PA E : Nat → Nat)
    (f x y : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun b ih => bIf(Nat.beq (trV G W PA f x (fld(E y, Nat.mul 14 b, 16383)))
      (trV G W PA f y (fld(E x, Nat.mul 14 b, 16383))), ih, true)) 5

@[expose] noncomputable def clsK (G : Nat → Nat) (W : Nat → List Nat) (PA E : Nat → Nat) (f : Nat)
    (c : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x r ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun y _ ih2 => bAnd(ncK G W PA E f x y, ih2)) r, ih)) c

@[expose] noncomputable def memMask (CL : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun c _ acc => List.rec (motive := fun _ => Nat) acc
      (fun x _ a => Nat.lor (Nat.shiftLeft 1 x) a) c) CL

@[expose] noncomputable def memAt (GI : Nat → Nat) (dR : List Nat) (N : Nat) (E Z SG MB : Nat → Nat)
    (mem k : Nat) : Bool :=
  strictB (actW GI dR (Z k)) fun u => strictB (Nat.shiftRight (MB k) 1) fun b =>
    bIf(Nat.beq (Nat.land (MB k) 1) 1,
      bAnd(Nat.blt b N, bAnd(Nat.beq (E b) u,
        Nat.beq (Nat.land (Nat.shiftRight mem k) 1) 1)),
      bAnd(Nat.ble b N, bAnd(bIf(Nat.beq b 0, true, Nat.blt (E (SG (Nat.sub b 1))) u),
        bIf(Nat.beq b N, true, Nat.blt u (E (SG b))))))

@[expose] noncomputable def recK (G GI : Nat → Nat) (W : Nat → List Nat) (nG N : Nat) (dR : List Nat)
    (E Z PA SG CT MB : Nat → Nat) (mem f k : Nat) : Bool :=
  bAnd(treeAt (fun t j => actW G (W j) t) B0 (fun j => j) nG E PA k,
  bAnd(treeAt (fun t j => actW G (W j) t) (Z 0) (fun j => j) nG Z PA k,
  bAnd(closedAt (fun t j => actW G (W j) t) (fun j => j) nG N E CT k,
  bAnd(sortAt N E SG k,
  bAnd(rootK PA f k, memAt GI dR N E Z SG MB mem k)))))

@[expose] noncomputable def grpK (G GI : Nat → Nat) (W : Nat → List Nat) (nG N : Nat)
    (dW dR : List Nat) (E Z PA SG CT MB : Nat → Nat) (CL : List (List Nat)) (f : Nat) : Bool :=
  bAnd(Nat.beq (Z 0) (actW G dW B0),
    strictB (memMask CL) fun mem =>
      bAnd(CFSG.KC.Enum.allN N (recK G GI W nG N dR E Z PA SG CT MB mem f),
        List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(clsK G W PA E f c, ih)) CL))

end CFSG.KC.HatHe

end
