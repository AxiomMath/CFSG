module

public import Certificates.Data.Kernel.SporSch.HNT0
public import Certificates.Data.Kernel.SporSch.HNXPtL
public import Certificates.Data.Kernel.SporSch.HNXPrim

public section

namespace CFSG.KS.HNT0

open CFSG.KC.Enum CFSG.KS.BaseEq CFSG.KC.LL CFSG.KC.LL.HNX

@[expose] noncomputable def packL (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) l

@[expose] noncomputable def omK (n N : Nat) (OM : List Nat) : Bool :=
  bAnd(Nat.beq (lenK OM) n, bAnd(allL OM (fun x => Nat.blt x N),
    strictB (packL (nat_lit 21) OM) fun P => allN n fun i =>
      strictB (fldW P (Nat.mul (nat_lit 21) i) (nat_lit 21)) fun x => allN i fun j =>
        bIf(Nat.beq (fldW P (Nat.mul (nat_lit 21) j) (nat_lit 21)) x, false, true)))

@[expose] noncomputable def rankK (n : Nat) (T : Nat → Nat) (CM3 M RI : Nat) (OM RK : List Nat) :
    Bool :=
  bAnd(Nat.beq (lenK RK) (nat_lit 133), bAnd(allL RK (fun x => Nat.blt x n),
    bAnd(CFSG.KS.SporSch.validHN RI,
    strictB (packL (nat_lit 21) OM) fun P => strictB (packL (nat_lit 8) RK) fun Q =>
    strictB (trM RI) fun G => allN (nat_lit 3) fun b => strictB (bCnt (nat_lit 133) b) fun c =>
    strictB (mulC CM3 (listA T M (packF (fun i => fldW P (Nat.mul (nat_lit 21)
      (fldW Q (Nat.mul (nat_lit 8) i) (nat_lit 8))) (nat_lit 21)) (Nat.mul (nat_lit 64) b) c) c) G)
      fun Y => allN c fun k => Nat.beq (fldW Y (Nat.mul (nat_lit 1729) k) (nat_lit 1729))
        (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 13) (Nat.add (Nat.mul (nat_lit 64) b) k))))))

@[expose] noncomputable def ptsK (n : Nat) (T : Nat → Nat) (MS CM3 M W : Nat) (OM : List Nat)
    (g : Nat) : Bool :=
  bAnd(allN n (fun i => Nat.blt (pg (nat_lit 8) (nat_lit 255) g i) n),
    strictB (packL (nat_lit 21) OM) fun P => strictB (trM W) fun G =>
      ptsFn T MS CM3 M G (fun i => fldW P (Nat.mul (nat_lit 21) i) (nat_lit 21))
        (fun i => fldW P (Nat.mul (nat_lit 21) (pg (nat_lit 8) (nat_lit 255) g i)) (nat_lit 21)) n)

@[expose] noncomputable def keyL (w m : Nat) (ps : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (pg w m t p) (Nat.shiftLeft ih w)) ps

@[expose] noncomputable def invK (w m : Nat) (ps : List Nat) (t : Nat) : Bool :=
  bAnd(sqFixK w m ps t, bIf(allL ps (fun p => Nat.beq (pg w m t p) p), false, true))

@[expose] noncomputable def censK (w m : Nat) (ps : List Nat) (T : Nat → Nat) (IM k : Nat) : Bool :=
  strictB fld(IM, k, nat_lit 1) fun bit => strictB (T k) fun t =>
    bIf(invK w m ps t, Nat.beq bit (nat_lit 1), Nat.beq bit (nat_lit 0))

@[expose] noncomputable def invLK (w m : Nat) (ps : List Nat) (N kw : Nat) (T IL : Nat → Nat)
    (KB : Nat) (l : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun x _ ih a lo => bAnd(Nat.ble lo x, bAnd(Nat.blt x N, strictB (T x) fun t =>
      bAnd(Nat.beq (IL a) t, bAnd(Nat.beq (fldW KB (Nat.mul kw a) kw) (keyL w m ps t),
        ih (Nat.succ a) (Nat.succ x)))))) l

@[expose] noncomputable def appK (w m np t k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.lor acc
    (Nat.shiftLeft (pg w m t (pg w m k i)) (Nat.mul w i))) np

@[expose] noncomputable def pairK (na w m np kw : Nat) (IL : Nat → Nat)
    (KB a ta ka row pr b : Nat) : Bool :=
  strictB (IL b) fun tb => strictB (appK w m np ta (fldW KB (Nat.mul kw b) kw)) fun x =>
  strictB (appK w m np tb ka) fun y => strictB fld(row, b, nat_lit 1) fun e =>
  strictB fld(row, Nat.add (nat_lit 1024) b, nat_lit 1) fun h =>
  strictB fld(pr, Nat.mul (nat_lit 10) b, nat_lit 1023) fun p =>
    bIf(bAnd(bIf(Nat.beq b a, false, true), Nat.beq x y),
      bAnd(Nat.beq e (nat_lit 1), bAnd(Nat.blt p na,
        bAnd(Nat.beq (fldW KB (Nat.mul kw p) kw) x,
          Nat.beq h (nIf(Nat.blt b p, nat_lit 1, nat_lit 0))))),
      bAnd(Nat.beq e (nat_lit 0), bAnd(Nat.beq h (nat_lit 0), Nat.beq p (nat_lit 0))))

@[expose] noncomputable def adjK (na w m : Nat) (ps : List Nat) (kw : Nat) (IL AL PR : Nat → Nat)
    (KB a : Nat) : Bool :=
  strictB (IL a) fun ta => strictB (AL a) fun row => strictB (PR a) fun pr =>
  strictB (keyL w m ps ta) fun ka => strictB (lenK ps) fun np =>
  bAnd(Nat.blt row (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 1024) na)),
    bAnd(Nat.beq (fldW row na (Nat.sub (nat_lit 1024) na)) (nat_lit 0),
    bAnd(Nat.blt pr (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 10) na)),
      allN na (pairK na w m np kw IL KB a ta ka row pr))))

end CFSG.KS.HNT0

end
