module

public import Certificates.Data.Kernel.McLNine.Defs

public section

namespace CFSG.KS.McLThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.McLAS CFSG.KS.Mathieu CFSG.KS.McLNine

@[expose] noncomputable def inO2 (n : Nat) : Bool :=
  bIf(Nat.beq n (nat_lit 262), true, Nat.beq n (nat_lit 272))

@[expose] noncomputable def inS (n : Nat) : Bool := bIf(Nat.beq n (nat_lit 200), true, inO2 n)

@[expose] noncomputable def gpt (G : Nat → Nat) (j q : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 3), q, pg (nat_lit 9) (mask (nat_lit 9)) (G j) q)

@[expose] noncomputable def o2K (G : Nat → Nat) (jw : Nat) : Bool :=
  bAnd(allN (nat_lit 3) (fun j => bAnd(inO2 (gpt G j (nat_lit 262)),
    inO2 (gpt G j (nat_lit 272)))),
  bAnd(Nat.blt jw (nat_lit 3), Nat.beq (gpt G jw (nat_lit 262)) (nat_lit 272)))

@[expose] noncomputable def ne3 (x y z : Nat) : Bool :=
  bIf(Nat.beq x y, false, bIf(Nat.beq x z, false, bIf(Nat.beq y z, false, true)))

@[expose] noncomputable def orbQ (G : Nat → Nat) (q a b c : Nat) : Bool :=
  bIf(inO2 q, true,
    bIf(Nat.beq a (nat_lit 4), allN (nat_lit 3) (fun j => Nat.beq (gpt G j q) q),
      bAnd(Nat.blt a (nat_lit 4), bAnd(Nat.blt b (nat_lit 4), bAnd(Nat.blt c (nat_lit 4),
        ne3 q (gpt G a q) (gpt G b (gpt G c q)))))))

@[expose] noncomputable def stabK (F : Nat → Nat) (w : List Nat) : Bool :=
  bAnd(inS (walkK F w (nat_lit 200)), bAnd(inS (walkK F w (nat_lit 262)),
    inS (walkK F w (nat_lit 272))))

@[expose] noncomputable def difK (F : Nat → Nat) (w v : List Nat) : Bool :=
  bIf(bAnd(Nat.beq (walkK F w (nat_lit 262)) (walkK F v (nat_lit 262)),
      Nat.beq (walkK F w (nat_lit 272)) (walkK F v (nat_lit 272))), false,
    bIf(bAnd(Nat.beq (walkK F w (nat_lit 262)) (walkK F v (nat_lit 272)),
      Nat.beq (walkK F w (nat_lit 272)) (walkK F v (nat_lit 262))), false, true))

@[expose] noncomputable def difAllK (F : Nat → Nat) (w : List Nat) (vs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ ih => bAnd(difK F w v, ih)) vs

@[expose] noncomputable def pairK (F : Nat → Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w rest ih => bAnd(difAllK F w rest, ih)) ws

@[expose] noncomputable def fixK (F : Nat → Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(Nat.beq (walkK F w (nat_lit 200)) (nat_lit 200), ih)) ws

@[expose] noncomputable def agK (F : Nat → Nat) (wa wg : List Nat) : Bool :=
  bAnd(stabK F wa, strictB (wK F wa) (fun a => bAnd(Nat.beq (pwK (nat_lit 3) a) idK,
    bAnd(bIf(Nat.beq a idK, false, true),
      strictB (wK F wg) (fun g => Nat.beq (pcK g a) (pcK (pcK a a) g))))))

@[expose] noncomputable def mcl3K (F G : Nat → Nat) (ws : List (List Nat)) (WA WB WC : List Nat)
    (jw : Nat) (p0w : List (List Nat)) (m0 m1 wa wg : List Nat) : Bool :=
  bAnd(wordsK F G ws (nat_lit 0), bAnd(o2K G jw,
  bAnd(allN (nat_lit 275) (fun q => orbQ G q (nget WA q) (nget WB q) (nget WC q)),
  bAnd(fixK F p0w, bAnd(pairK F p0w,
  bAnd(stabK F m0, bAnd(stabK F m1,
  bAnd(Nat.beq (walkK F m0 (nat_lit 200)) (nat_lit 262),
  bAnd(Nat.beq (walkK F m1 (nat_lit 200)) (nat_lit 272), agK F wa wg)))))))))

end CFSG.KS.McLThree

end
