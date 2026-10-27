module

public import Certificates.Data.Kernel.IdxFourSiftK

public section

namespace CFSG.KC.IF4L

open CFSG.KC.IF4C CFSG.KC.IF4R

@[expose] noncomputable def xsel (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih x => Nat.xor (bif Nat.beq (Nat.mod x 2) 1 then a else 0) (ih (Nat.div x 2))) l x

@[expose] noncomputable def wact (CM : List (List Nat)) (w : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun s _ ih m => xsel (nthD [] CM s) (ih m)) w m

@[expose] noncomputable def lettersOK (n : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => Nat.blt s n && ih) w

@[expose] noncomputable def nodupN (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => !memN a t && ih) l

@[expose] noncomputable def par6 (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih x => Bool.xor (Nat.beq (Nat.land x 1) 1) (ih (Nat.shiftRight x 1))) 6 x

@[expose] noncomputable def f0K (m n : Nat) : Bool :=
  par6 (Nat.xor (Nat.land m (Nat.shiftRight n 6)) (Nat.land (Nat.shiftRight m 6) n))

@[expose] noncomputable def commOK (LP : List Nat) : Bool :=
  allBelow (lenN LP) fun i => Nat.beq (mulP (nthD 0 LP i) (nthD 0 LP i)) idP &&
    allBelow i fun j =>
      Nat.beq (mulP (nthD 0 LP i) (nthD 0 LP j)) (mulP (nthD 0 LP j) (nthD 0 LP i))

@[expose] noncomputable def subOK (LP : List Nat) : Bool :=
  allBelow (Nat.sub (Nat.pow 2 (lenN LP)) 1) fun m => !Nat.beq (subP LP (Nat.succ m)) idP

@[expose] noncomputable def conjOK (SG LP : List Nat) (CM : List (List Nat)) : Bool :=
  Nat.beq (lenN CM) (lenN SG) && allBelow (lenN SG) fun s =>
    Nat.beq (lenN (nthD [] CM s)) (lenN LP) && allBelow (lenN LP) fun i =>
      Nat.blt (nthD 0 (nthD [] CM s) i) (Nat.pow 2 (lenN LP)) &&
        Nat.beq (mulP (nthD 0 SG s) (nthD 0 LP i))
          (mulP (subP LP (nthD 0 (nthD [] CM s) i)) (nthD 0 SG s))

@[expose] noncomputable def orbOK (CM : List (List Nat)) (r : Nat) (ws : List (List Nat))
    (ms : List Nat) : Bool :=
  Nat.beq (lenN ws) (lenN ms) && allBelow (lenN ms) fun k =>
    lettersOK (lenN CM) (nthD [] ws k) && Nat.beq (wact CM (nthD [] ws k) r) (nthD 0 ms k)

@[expose] noncomputable def levelOK (CM : List (List Nat)) (τ : List Nat) (k : Nat)
    (ws : List (List Nat)) : Bool :=
  ws.all (fun w => lettersOK (lenN CM) w &&
    allBelow k fun j => Nat.beq (wact CM w (nthD 0 τ j)) (nthD 0 τ j)) &&
  nodupN (ws.map fun w => wact CM w (nthD 0 τ k))

@[expose] noncomputable def prodLen (TT : List (List (List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) 1 (fun ws _ ih => Nat.mul (lenN ws) ih) TT

@[expose] noncomputable def chainOK (CM : List (List Nat)) (ms τ : List Nat)
    (TT : List (List (List Nat))) (n : Nat) : Bool :=
  τ.all (fun t => memN t ms) && Nat.beq (lenN TT) (lenN τ) &&
    allBelow (lenN τ) (fun k => levelOK CM τ k (nthD [] TT k)) && Nat.ble n (prodLen TT)

@[expose] noncomputable def inW (a b x : Nat) : Bool := !f0K x a && !f0K x b

@[expose] noncomputable def imgs (LP WB : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun l _ ih => List.rec (motive := fun _ => List Nat) ih
      (fun w _ r => Nat.xor (ap12 l w) w :: r) WB) LP

@[expose] noncomputable def selOK (B l cs : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun cs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs)
    (fun x _ ih cs => List.rec (motive := fun _ => Bool) false
      (fun c cs' _ => Nat.beq x (xsel B c) && ih cs') cs) l cs

@[expose] noncomputable def wOK (LP VB WB WC : List Nat) (Bi : Nat) (CO VW : List Nat)
    (a b : Nat) : Bool :=
  WB.all (inW a b) && LP.all (fun l => WB.all fun w => inW a b (ap12 l w)) &&
    selOK VB (imgs LP WB) CO && selOK (imgs LP WB) VB VW &&
    Nat.beq (lenN WB) 10 && Nat.beq (lenN WC) 2 && Nat.beq (mulP (packL (WB ++ WC)) Bi) idP &&
    !f0K (nthD 0 WC 0) a && f0K (nthD 0 WC 0) b && f0K (nthD 0 WC 1) a && !f0K (nthD 0 WC 1) b

end CFSG.KC.IF4L

end
