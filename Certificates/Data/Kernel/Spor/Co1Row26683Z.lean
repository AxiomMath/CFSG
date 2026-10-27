module

public import Certificates.Data.Kernel.Spor.Co1Row26683K
public import Certificates.Data.Kernel.Co1BTri
public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KS.Co1Row26683Z

open CFSG.KC.Enum CFSG.KS.Co1Row26683

@[expose] noncomputable def wvI (X Y Xi Yi : Nat) (w : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun c _ ih q => strictN (ap (lp Xi Yi X Y c) q) ih) w q

@[expose] noncomputable def triZK (Z PT P : Nat) : Bool :=
  strictB (CFSG.KC.Co1F2.trK (nat_lit 24) Z) fun T =>
    bAnd(CFSG.KC.Co1T.triWK T PT P (nat_lit 0) (nat_lit 1365),
      invoOK (nat_lit 1365) (nat_lit 11) (CFSG.KS.mask (nat_lit 11)) (nat_lit 15015) P)

@[expose] noncomputable def zqK (X Y Xi Yi P : Nat) (WC ZQ : List (List Nat)) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun b => Nat.beq (nthN (nthW ZQ (nat_lit 0)) b) (ap P b)) (nat_lit 3),
    allBlk (nat_lit 0) (fun i => allBlk (nat_lit 0) (fun b =>
      Nat.beq (nthN (nthW ZQ (Nat.succ i)) b)
        (wv X Y Xi Yi (nthW WC i) (ap P (wvI X Y Xi Yi (nthW WC i) b)))) (nat_lit 3)) (nat_lit 2))

@[expose] noncomputable def movedK (S : Nat → Nat) (r : Nat) : Bool :=
  Bool.not (allBlk (nat_lit 2) (fun i => Nat.beq (pg (nat_lit 11) (nat_lit 2047) (S i) r) r)
    (nat_lit 4))

@[expose] noncomputable def primK (S : Nat → Nat) (reps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(movedK S r, ih)) reps

end CFSG.KS.Co1Row26683Z

end
