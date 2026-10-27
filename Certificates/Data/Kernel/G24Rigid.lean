module

public import Certificates.Data.Kernel.G24Key

public section

namespace CFSG.KC.G24Rigid

open CFSG.KC.Enum CFSG.KC.G24Key

@[expose] noncomputable def wG (F : Nat → Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun c _ ih p => strictN (ih p) (F c)) w p

@[expose] noncomputable def itN (f : Nat → Nat) (e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => strictN ih f) e

@[expose] noncomputable def tlet (Z : Nat → Nat) (B : Nat → Nat) (c q : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), Z q, ap (B (Nat.sub c (nat_lit 1))) q)

@[expose] noncomputable def fixN (f : Nat → Nat) (e : Nat) : Bool :=
  allN (nat_lit 3) (fun b => Nat.beq (itN f e b) b)

@[expose] noncomputable def ordK (F : Nat → Nat → Nat) (w : List Nat) (v : Nat) : Bool :=
  bAnd(fixN (wG F w) v, allN v (fun d =>
    bIf(Nat.beq d (nat_lit 0), true, bIf(fixN (wG F w) d, false, true))))

@[expose] noncomputable def ownK (F : Nat → Nat → Nat) (T : List (List Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun t _ ih => bAnd(ordK F t.1 t.2, ih)) T

@[expose] noncomputable def refK (F : Nat → Nat → Nat) (T : List (List Nat × Nat)) (r : Nat) :
    Bool :=
  strictB (Nat.sub r (nat_lit 1)) (fun q =>
  strictB (Nat.land q (nat_lit 31)) (fun t =>
  strictB (Nat.shiftRight q (nat_lit 5)) (fun m =>
    bAnd(Nat.blt t T.length,
      bIf(Nat.blt m (nat_lit 3),
        bIf(Nat.beq (itN (wG F (T.getD t ([], 0)).1) (T.getD t ([], 0)).2 m) m, false, true),
        bAnd(Nat.blt (Nat.sub m (nat_lit 2)) (T.getD t ([], 0)).2,
          fixN (wG F (T.getD t ([], 0)).1) (Nat.sub m (nat_lit 2))))))))

@[expose] noncomputable def levK (F : Nat → Nat → Nat → Nat) (T : List (List Nat × Nat))
    (R SK : Nat → Nat) (n : Nat) : Bool :=
  allN n (fun k => strictB (R k) (fun r =>
    bIf(Nat.beq r (nat_lit 0), true, bIf(Nat.beq (SK k) (nat_lit 0), refK (F k) T r, true))))

@[expose] noncomputable def cntK (R SK : Nat → Nat) (n : Nat) : Nat :=
  foldN n (fun k s => nIf(bAnd(Nat.beq (R k) (nat_lit 0), Nat.beq (SK k) (nat_lit 0)),
    Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def slpK (S A : Nat → Nat) (n : Nat) : Bool :=
  allN (Nat.sub n (nat_lit 2)) (fun i => strictB (Nat.add i (nat_lit 2)) (fun j =>
    strictB (Nat.land (A j) (nat_lit 15)) (fun a => strictB (Nat.shiftRight (A j) (nat_lit 4))
      (fun b => bAnd(Nat.blt a j, bAnd(Nat.blt b j,
        allN (nat_lit 1365) (fun p => Nat.beq (ap (S j) p) (ap (S a) (ap (S b) p)))))))))

@[expose] noncomputable def invK (S SI : Nat → Nat) (n : Nat) : Bool :=
  allN n (fun j => allN (nat_lit 1365) (fun p => Nat.beq (ap (SI j) (ap (S j) p)) p))

@[expose] noncomputable def ptEqK (P : Nat) (f : Nat → Nat) : Bool :=
  allN (nat_lit 1365) (fun p => Nat.beq (ap P p) (f p))

@[expose] noncomputable def wpB (B W : Nat → Nat) (L p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p
    (fun i ih => strictN ih (ap (B (Nat.land (tw (nat_lit 4) (nat_lit 15) W i) (nat_lit 3))))) L

end CFSG.KC.G24Rigid

end
