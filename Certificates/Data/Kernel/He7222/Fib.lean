module

public import Certificates.Data.Kernel.He7222.Cls

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow

@[expose] noncomputable def srEq (w m : Nat) (h hI : Nat) (ss cn cni cr cri ks : List Nat) : Bool :=
  allN (nat_lit 5) (fun p =>
    Nat.beq (cjEv w m cn ss cni (pg w m hI (evK w m ks (pg w m h p))))
      (pg w m hI (evK w m ks (pg w m h (cjEv w m cr ss cri p)))))

@[expose] noncomputable def srK (w m : Nat) (Ts TIs KTs : List (List Nat)) (ss : List Nat)
    (h hI nr : Nat) (KC : List (List Nat)) (XR Sv : List Nat) (SR : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.beq q (lenS Sv))
    (fun rec _ ih q => List.rec (motive := fun _ => Bool) false
      (fun r k _ => strictB (getS Sv q) (fun n => strictB (getS XR r) (fun xr =>
        bAnd(Nat.blt r nr, bAnd(tupOK KTs k,
          bAnd(srEq w m h hI ss (stkK Ts (getLs KC n)) (stkIK TIs (getLs KC n) List.nil)
              (stkK Ts (getLs KC xr)) (stkIK TIs (getLs KC xr) List.nil) (stkK KTs k),
            strictB (Nat.succ q) ih))))))
      rec)
    SR (nat_lit 0)

@[expose] noncomputable def cycN (f : Nat → Nat) (p F : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih q l => strictN (f q) (fun q' => nIf(Nat.beq q' p, l, ih q' (Nat.succ l))))
    F p (nat_lit 1)

@[expose] noncomputable def dvK (e l : Nat) : Bool := Nat.beq (Nat.mod e l) (nat_lit 0)

@[expose] noncomputable def dv3 (l : Nat) : Bool :=
  bIf(dvK (nat_lit 25) l, true, bIf(dvK (nat_lit 343) l, true, dvK (nat_lit 17) l))

@[expose] noncomputable def dv5 (x a b c d e : Nat) : Bool :=
  bAnd(dvK x a, bAnd(dvK x b, bAnd(dvK x c, bAnd(dvK x d, dvK x e))))

@[expose] noncomputable def okK (f : Nat → Nat) : Bool :=
  strictB (cycN f (nat_lit 0) (nat_lit 343)) (fun l0 => bIf(dv3 l0,
    strictB (cycN f (nat_lit 1) (nat_lit 343)) (fun l1 =>
    strictB (cycN f (nat_lit 2) (nat_lit 343)) (fun l2 =>
    strictB (cycN f (nat_lit 3) (nat_lit 343)) (fun l3 =>
    strictB (cycN f (nat_lit 4) (nat_lit 343)) (fun l4 =>
      bIf(dv5 (nat_lit 25) l0 l1 l2 l3 l4, true,
        bIf(dv5 (nat_lit 343) l0 l1 l2 l3 l4, true, dv5 (nat_lit 17) l0 l1 l2 l3 l4)))))),
    false))

@[expose] noncomputable def conjYK (w m : Nat) (gs ks k2s kts : List Nat) : Bool :=
  allN (nat_lit 5) (fun p =>
    Nat.beq (evK w m gs (evK w m ks (evK w m k2s p))) (evK w m k2s (evK w m gs (evK w m kts p))))

@[expose] noncomputable def fleafK (w m : Nat) (KTs : List (List Nat)) (gs : List Nat)
    (FT : List (List Nat)) (ks : List Nat) (i : Nat) (st : List (List Nat))
    (k : Nat → List (List Nat) → Bool) : Bool :=
  strictB (Nat.succ i) (fun i' =>
    List.rec (motive := fun _ => Bool)
      (bIf(okK (fun p => evK w m gs (evK w m ks p)), false, k i' st))
      (fun rec rest _ => List.rec (motive := fun _ => Bool) false
        (fun ri tk _ => bIf(Nat.beq ri i,
          List.rec (motive := fun _ => Bool) false
            (fun t k2 _ => bAnd(tupOK KTs k2,
              bAnd(conjYK w m gs ks (stkK KTs k2) (stkK KTs (getLs FT t)), k i' rest)))
            tk,
          bIf(okK (fun p => evK w m gs (evK w m ks p)), false, k i' st)))
        rec)
      st)

@[expose] noncomputable def fwalkK (w m : Nat) (KTs : List (List Nat)) (gs : List Nat)
    (FT : List (List Nat)) :
    List (List Nat) → List Nat → Nat → List (List Nat) → (Nat → List (List Nat) → Bool) → Bool :=
  List.rec
    (motive := fun _ => List Nat → Nat → List (List Nat) → (Nat → List (List Nat) → Bool) → Bool)
    (fun stack i st k => fleafK w m KTs gs FT stack i st k)
    (fun lvl _ ih stack i st k =>
      List.rec
        (motive := fun _ => Nat → List (List Nat) → (Nat → List (List Nat) → Bool) → Bool)
        (fun i st k => k i st)
        (fun t _ ihT i st k => ih (List.cons t stack) i st (fun i' st' => ihT i' st' k))
        lvl i st k)

@[expose] noncomputable def fibK (w m : Nat) (KTs Ls : List (List Nat)) (gs : List Nat)
    (FR FT : List (List Nat)) : Bool :=
  fwalkK w m KTs gs FT Ls List.nil (nat_lit 0) FR
    (fun _ st => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) st)

end CFSG.KC.HeChain

end
