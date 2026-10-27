module

public import Certificates.Data.Kernel.Spor.TBfs

public section

namespace CFSG.KS.PC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def lvK (L : Nat → Nat → Nat) (B : Nat → Nat) (NL i : Nat) : List Nat :=
  (List.range NL).filter fun l => allN i fun j => Nat.beq (L l (B j)) (B j)

@[expose] noncomputable def lvAt (L : Nat → Nat → Nat) (B : Nat → Nat) (NL i t : Nat) : Nat :=
  List.getD (lvK L B NL i) t (nat_lit 0)

@[expose] noncomputable def mapK (f : Nat → Nat) (q : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (f x) ih) q

@[expose] noncomputable def listEqK (a b : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y r _ => bAnd(Nat.beq x y, ih r)) b) a b

@[expose] noncomputable def walkF (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f k : Nat)
    (q : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ q => q)
    (fun _ ih k q => Bool.rec (motive := fun _ => List Nat) q
      (mapK (L (r32 LAB k)) (ih (r32 PAR k) q))
      (bAnd(Nat.blt (nat_lit 0) k, Nat.blt (r32 PAR k) k))) f k q

@[expose] noncomputable def walkK (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (k : Nat)
    (q : List Nat) : List Nat :=
  walkF L PAR LAB k k q

@[expose] noncomputable def walkInvF (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f k : Nat)
    (q : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ q => q)
    (fun _ ih k q => Bool.rec (motive := fun _ => List Nat) q
      (ih (r32 PAR k) (mapK (L (Nat.xor (r32 LAB k) (nat_lit 1))) q))
      (bAnd(Nat.blt (nat_lit 0) k, Nat.blt (r32 PAR k) k))) f k q

@[expose] noncomputable def walkInvK (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (k : Nat)
    (q : List Nat) : List Nat :=
  walkInvF L PAR LAB k k q

@[expose] noncomputable def siftF (L : Nat → Nat → Nat) (POS PAR LAB : Nat → Nat → Nat)
    (CNT QB : Nat → Nat) (Q : List Nat) (f i : Nat) (q : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ q => listEqK q Q)
    (fun _ ih i q => strictB (r32 (POS i) (List.getD q (QB i) (nat_lit 0))) fun k =>
      bAnd(Nat.blt k (CNT i), ih (Nat.succ i) (walkInvK L (PAR i) (LAB i) k q))) f i q

@[expose] noncomputable def siftK (L : Nat → Nat → Nat) (POS PAR LAB : Nat → Nat → Nat)
    (CNT QB : Nat → Nat) (Q : List Nat) (m i : Nat) (q : List Nat) : Bool :=
  siftF L POS PAR LAB CNT QB Q (Nat.sub m i) i q

@[expose] noncomputable def schK (L : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat)
    (CNT QB : Nat → Nat) (Q : List Nat) (m i l k : Nat) : Bool :=
  strictB (r32 (POS i) (L l (r32 (PTS i) k))) fun ky =>
    bAnd(Nat.blt ky (CNT i), siftK L POS PAR LAB CNT QB Q m (Nat.succ i)
      (walkInvK L (PAR i) (LAB i) ky (mapK (L l) (walkK L (PAR i) (LAB i) k Q))))

@[expose] noncomputable def schSlK (L : Nat → Nat → Nat) (B : Nat → Nat) (NL : Nat)
    (PTS POS PAR LAB : Nat → Nat → Nat) (CNT QB : Nat → Nat) (Q : List Nat) (m i lo len : Nat) :
    Bool :=
  strictB (List.length (lvK L B NL i)) fun r =>
    allN len fun d => strictB (Nat.add lo d) fun k =>
      bIf(Nat.blt k (CNT i), allN r fun t => schK L PTS POS PAR LAB CNT QB Q m i (lvAt L B NL i t) k,
        true)

@[expose] noncomputable def invK (L : Nat → Nat → Nat) (n NL : Nat) : Bool :=
  allN (Nat.div NL (nat_lit 2)) fun j => allN n fun x =>
    strictB (L (Nat.mul (nat_lit 2) j) x) fun y =>
      bAnd(Nat.blt y n, bAnd(Nat.blt (L (Nat.succ (Nat.mul (nat_lit 2) j)) x) n,
        Nat.beq (L (Nat.succ (Nat.mul (nat_lit 2) j)) y) x))

@[expose] noncomputable def termK (L : Nat → Nat → Nat) (B : Nat → Nat) (NL m : Nat) (Q : List Nat) :
    Bool :=
  List.all (lvK L B NL m) fun l => listEqK (mapK (L l) Q) Q

end CFSG.KS.PC

end
