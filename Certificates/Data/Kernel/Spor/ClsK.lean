module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.PSearch

public section

namespace CFSG.KS.ClsK

open CFSG.KC.Enum CFSG.KS.PSearch

@[expose] noncomputable def itP (w m x k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => pg w m x ih) k

@[expose] noncomputable def movK (w m x k : Nat) (ks : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => bIf(Nat.beq (itP w m x k p) p, ih, true)) ks

@[expose] noncomputable def cjK (w m h r x : Nat) (ks : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(Nat.beq (pg w m h (pg w m r p)) (pg w m x (pg w m h p)), ih)) ks

@[expose] noncomputable def ptK (w m idn N : Nat) (T : Nat → Nat) (ks reps : List Nat)
    (i t : Nat) : Bool :=
  strictB (T i) fun x =>
    bAnd(bIf(Nat.beq x idn, true, movK w m x (nat_lit 1) ks),
      bIf(Nat.beq t (nat_lit 0),
        bIf(Nat.beq x idn, true, bAnd(movK w m x (nat_lit 2) ks, movK w m x (nat_lit 5) ks)),
        strictB (Nat.sub t (nat_lit 1)) fun u =>
          bAnd(Nat.blt (Nat.mod u (nat_lit 4)) (List.length reps),
          bAnd(Nat.blt (Nat.div u (nat_lit 4)) N,
            cjK w m (T (Nat.div u (nat_lit 4))) (T (nthN reps (Nat.mod u (nat_lit 4)))) x ks))))

@[expose] noncomputable def tagsK (w m idn N : Nat) (T : Nat → Nat) (ks reps : List Nat) :
    List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih i => bAnd(ptK w m idn N T ks reps i t, ih (Nat.succ i)))

@[expose] noncomputable def cntK (c : Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t _ ih => nIf(Nat.beq t (nat_lit 0), ih,
      nIf(Nat.beq (Nat.mod (Nat.sub t (nat_lit 1)) (nat_lit 4)) c, Nat.succ ih, ih)))

@[expose] noncomputable def clsK (w m idn N : Nat) (T : Nat → Nat) (ks reps tg : List Nat)
    (b : Nat) : Bool :=
  bAnd(Nat.beq (List.length tg) N,
  bAnd(tagsK w m idn N T ks reps tg (nat_lit 0),
  bAnd(Nat.ble (List.length reps) (nat_lit 4),
    allN (List.length reps) fun c =>
      bAnd(Nat.blt (nthN reps c) N, Nat.ble b (cntK c tg)))))

end CFSG.KS.ClsK

end
