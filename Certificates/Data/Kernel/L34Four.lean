module

public import Certificates.Data.Kernel.J3Four

public section

namespace CFSG.KD.L34Four

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ
open CFSG.KD.J3Four (getN lenN letOK conjOK lenR)

@[expose] noncomputable def pm (x y : Nat) : Nat := pmN (nat_lit 42) (nat_lit 13) x y

@[expose] noncomputable def eq (x y : Nat) : Bool := eqN (nat_lit 42) (nat_lit 13) x y

@[expose] noncomputable def one : Nat := pidn (nat_lit 42) (nat_lit 13)

@[expose] noncomputable def getW (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def lenW (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def wordN (G : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun a _ ih => pm (getN G a) ih) w

@[expose] noncomputable def powSq : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih b e acc =>
      strictN (nIf(Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1), pm b acc, acc)) fun acc' =>
        strictN (pm b b) fun b' => ih b' (Nat.shiftRight e (nat_lit 1)) acc')

@[expose] noncomputable def ordOK (x : Nat) (p : Nat) : Bool :=
  bAnd(Nat.blt p (nat_lit 32), bAnd(eq (powSq (nat_lit 5) x p one) one, bIf(eq x one, false, true)))

@[expose] noncomputable def cgOK (G : List Nat) (r : Nat) (W : List (List Nat)) (Gc Gci : List Nat) :
    Bool :=
  bAnd(Nat.beq (lenW W) (lenN Gc), bAnd(Nat.beq (lenN Gci) (lenN Gc),
    allN (lenN Gc) fun j => strictB (getN Gc j) fun g =>
      bAnd(letOK (lenN G) (getW W j), bAnd(eq (wordN G (getW W j)) g,
        bAnd(eq (pm (getN Gci j) g) one, eq (pm g r) (pm r g))))))

@[expose] noncomputable def rowL (G : List Nat) (i : Nat) (W : List (List Nat)) (Gc Gci : List Nat)
    (wx : List Nat) (p : Nat) (pts : List Nat) (R : List (Nat × List Nat)) (c : Nat) : Bool :=
  bAnd(Nat.blt i (lenN G), strictB (getN G i) fun r => bAnd(cgOK G r W Gc Gci,
    bAnd(Nat.beq (lenR R) c, bAnd(letOK (lenN Gc) wx,
      strictB (wordN Gc wx) fun x => bAnd(ordOK x p, conjOK Gc Gci x pts R)))))

end CFSG.KD.L34Four

end
