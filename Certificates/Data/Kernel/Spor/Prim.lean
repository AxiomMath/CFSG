module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Prim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def canonK (n w m nw p : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.beq (Nat.shiftRight p nw) (nat_lit 0),
    allN n (fun i => Nat.blt (pg w m p i) n)))

@[expose] noncomputable def commK (n w m nw p q : Nat) : Bool :=
  bAnd(canonK n w m nw p, bAnd(canonK n w m nw q,
    Nat.beq (pcomp n w m p q) (pcomp n w m q p)))

@[expose] noncomputable def sqIdK (n w m nw idn p : Nat) : Bool :=
  bAnd(canonK n w m nw p, Nat.beq (pcomp n w m p p) idn)

@[expose] noncomputable def neIdK (n w m nw idn p : Nat) : Bool :=
  bAnd(canonK n w m nw p, bIf(Nat.beq p idn, false, true))

@[expose] noncomputable def center3K (n w m nw idn : Nat) (S LR TR : Nat → Nat) (kG z : Nat) :
    Bool :=
  strictB (LR (nat_lit 0)) (fun R0 => strictB (LR (nat_lit 1)) (fun R1 =>
  strictB (LR (nat_lit 2)) (fun R2 =>
  allN (rcnt R0) (fun a => strictB (TR (Nat.add (roff n nw R0) a)) (fun ta =>
  allN (rcnt R1) (fun b => strictB (pcomp n w m ta (TR (Nat.add (roff n nw R1) b))) (fun tab =>
  allN (rcnt R2) (fun c => strictB (pcomp n w m tab (TR (Nat.add (roff n nw R2) c))) (fun g =>
    bIf(allN kG (fun k => strictB (S k) (fun s =>
        Nat.beq (pcomp n w m g s) (pcomp n w m s g))),
      bIf(Nat.beq g idn, true, Nat.beq g z), true))))))))))

@[expose] noncomputable def compEqK (n w m nw p q r : Nat) : Bool :=
  bAnd(canonK n w m nw p, bAnd(canonK n w m nw q, Nat.beq (pcomp n w m p q) r))

@[expose] noncomputable def invEqK (n w m nw p r : Nat) : Bool := permOK n w m nw p r

@[expose] noncomputable def powEqK (n w m nw idn p e r : Nat) : Bool :=
  bAnd(canonK n w m nw p, Nat.beq (ppow n w m idn p e) r)

@[expose] noncomputable def eqK (p q : Nat) : Bool := Nat.beq p q

@[expose] noncomputable def neK (n w m nw p q : Nat) : Bool :=
  bAnd(canonK n w m nw p, bAnd(canonK n w m nw q, bIf(Nat.beq p q, false, true)))

@[expose] noncomputable def wordEqK (n w m idn : Nat) (S SI : Nat → Nat) (kS : Nat) (wd : List Int)
    (r : Nat) : Bool :=
  bAnd(szOK n w, bAnd(lettersK kS wd, Nat.beq (wordK n w m idn S SI wd) r))

@[expose] noncomputable def idK (n w m : Nat) : Bool :=
  allN n (fun i => Nat.beq (pg w m (pidn n w) i) i)

@[expose] noncomputable def fixedK (n w m p : Nat) (L : List Nat) : Bool :=
  Nat.rec (motive := fun _ => List Nat → Nat → Bool)
    (fun L _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun _ ih L i => bIf(Nat.beq (pg w m p i) i,
      List.rec (motive := fun _ => Bool) false (fun x xs _ => bAnd(Nat.beq x i, ih xs (Nat.succ i))) L,
      ih L (Nat.succ i)))
    n L (nat_lit 0)

end CFSG.KS.Prim

end
