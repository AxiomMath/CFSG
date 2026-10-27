module

public import Certificates.Data.Kernel.Fi23Nt.EnumDefs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum

@[expose] noncomputable def tmK (PAR : Nat) (LT : List Nat) (f : Nat) : Nat → Nat → Nat :=
  fun a b => Nat.rec (motive := fun _ => Nat → Nat) (fun _ => b)
    (fun _ ih a => nIf(Nat.beq a (nat_lit 0), b,
      strictN (lnK (nat_lit 16) PAR a) fun q =>
        strictN (ih (Nat.shiftRight q (nat_lit 2))) (ltK LT (Nat.land q (nat_lit 3))))) f a

@[expose] noncomputable def appK (u v : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) v (fun x _ ih => x :: ih) u

@[expose] noncomputable def rinvK (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => appK ih [Nat.xor x (nat_lit 1)]) w

@[expose] noncomputable def eqLK (u : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun v => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v)
    (fun x _ ih v => List.rec (motive := fun _ => Bool) false
      (fun y t _ => bAnd(Nat.beq x y, ih t)) v) u

@[expose] noncomputable def wdK (W : List (List Nat)) (PAR f : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => Bool.rec (motive := fun _ => List Nat)
      (appK (List.getD W (Nat.land (lnK (nat_lit 16) PAR i) (nat_lit 3)) [])
        (ih (Nat.shiftRight (lnK (nat_lit 16) PAR i) (nat_lit 2))))
      [] (Nat.beq i (nat_lit 0))) f

@[expose] noncomputable def aK (A k : Nat) : Nat := lnK (nat_lit 16) A k

@[expose] noncomputable def mskK (A : Nat) : Nat :=
  foldBlk (nat_lit 0) (fun k s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (aK A k))) (nat_lit 81)
    (nat_lit 0)

@[expose] noncomputable def bitK (M x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M x) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def subHK (n A : Nat) : Bool :=
  bAnd(Nat.beq (aK A (nat_lit 0)) (nat_lit 0), bAnd(Nat.blt (aK A (nat_lit 80)) n,
    allN (nat_lit 80) fun k => Nat.blt (aK A k) (aK A (Nat.succ k))))

@[expose] noncomputable def subIK (n PAR : Nat) (LT : List Nat) (A M k : Nat) : Bool :=
  strictB (aK A k) fun a =>
    bAnd(Nat.beq (tmK PAR LT n a (tmK PAR LT n a a)) (nat_lit 0),
      allN (nat_lit 81) fun l => strictB (aK A l) fun b => strictB (tmK PAR LT n a b) fun c =>
        bAnd(bitK M c, Nat.beq c (tmK PAR LT n b a)))

@[expose] noncomputable def repK (R c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ => lnK (nat_lit 16) R c) c

@[expose] noncomputable def cosIK (n PAR : Nat) (LT : List Nat) (A R nr D x : Nat) : Bool :=
  strictB (lnK (nat_lit 16) D x) fun d => strictB (Nat.shiftRight d (nat_lit 7)) fun c =>
    strictB (Nat.land d (nat_lit 127)) fun k =>
      bAnd(Nat.blt k (nat_lit 81), bAnd(Nat.ble c nr, bAnd(Nat.blt (repK R c) n,
        Nat.beq (tmK PAR LT n (repK R c) (aK A k)) x)))

@[expose] noncomputable def centCK (n PAR : Nat) (LT : List Nat) (A r : Nat) : Nat :=
  foldBlk (nat_lit 0) (fun l s => strictN (aK A l) fun b =>
    nIf(Nat.beq (tmK PAR LT n r b) (tmK PAR LT n b r), Nat.succ s, s)) (nat_lit 81) (nat_lit 0)

@[expose] noncomputable def centIK (n PAR : Nat) (LT : List Nat) (A bd r : Nat) : Bool :=
  Nat.blt (centCK n PAR LT A r) bd

@[expose] noncomputable def zCK (n PAR : Nat) (LT : List Nat) (A : Nat) : Nat :=
  foldBlk (nat_lit 0) (fun l s => strictN (aK A l) fun b =>
    nIf(allN (nat_lit 3) (fun j => Nat.beq (ltK LT j b) (tmK PAR LT n b (ltK LT j (nat_lit 0)))),
      Nat.succ s, s)) (nat_lit 81) (nat_lit 0)

@[expose] noncomputable def zK (n PAR : Nat) (LT : List Nat) (A bd : Nat) : Bool :=
  Nat.blt (zCK n PAR LT A) bd

@[expose] noncomputable def lnkUK (W : List (List Nat)) (PAR n A : Nat)
    (u : List Nat → List Nat) (I : List Nat) (Ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun Ws => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Ws)
    (fun i _ ih Ws => List.rec (motive := fun _ => Bool) false
      (fun w t _ => bAnd(Nat.blt i n, bAnd(bitK (mskK A) i,
        bAnd(eqLK w (u (wdK W PAR n i)), ih t)))) Ws) I Ws

@[expose] noncomputable def lnkK (W : List (List Nat)) (PAR n A : Nat) (I : List Nat)
    (Ws : List (List Nat)) : Bool :=
  lnkUK W PAR n A (fun v => v) I Ws

@[expose] noncomputable def lnkHK (W : List (List Nat)) (PAR n A : Nat) (h I : List Nat)
    (Ws : List (List Nat)) : Bool :=
  lnkUK W PAR n A (fun v => appK h (appK v (rinvK h))) I Ws

@[expose] noncomputable def fstK (S : List (List Nat × Bool)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [] (fun s _ ih => s.1 :: ih) S

@[expose] noncomputable def pwK (n PAR : Nat) (LT : List Nat) (a e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ ih => tmK PAR LT n a ih) e

@[expose] noncomputable def genIK (n PAR : Nat) (LT : List Nat) (A : Nat) (a : List Nat)
    (E k : Nat) : Bool :=
  strictB (lnK (nat_lit 8) E k) fun e =>
    Nat.beq (tmK PAR LT n (pwK n PAR LT (List.getD a (nat_lit 0) (nat_lit 0)) (lnK (nat_lit 2) e (nat_lit 0)))
      (tmK PAR LT n (pwK n PAR LT (List.getD a (nat_lit 1) (nat_lit 0)) (lnK (nat_lit 2) e (nat_lit 1)))
        (tmK PAR LT n (pwK n PAR LT (List.getD a (nat_lit 2) (nat_lit 0)) (lnK (nat_lit 2) e (nat_lit 2)))
          (pwK n PAR LT (List.getD a (nat_lit 3) (nat_lit 0)) (lnK (nat_lit 2) e (nat_lit 3))))))
      (aK A k)

@[expose] noncomputable def genK (n PAR : Nat) (LT : List Nat) (A : Nat) (a : List Nat) (E : Nat) :
    Bool :=
  bAnd(allN (nat_lit 4) (fun i => bitK (mskK A) (List.getD a i (nat_lit 0))),
    allN (nat_lit 81) (genIK n PAR LT A a E))

end CFSG.KC.Fi23Nt

end
