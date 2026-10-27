module

public import Certificates.Data.Kernel.Misc.RuBigZE

public section

namespace CFSG.KC.Misc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def img4 (f : Nat → Nat) : Nat :=
  foldN (nat_lit 4) (fun b acc => Nat.lor acc (Nat.shiftLeft (f b) (Nat.mul (nat_lit 12) b)))
    (nat_lit 0)

@[expose] noncomputable def lAp (A AI : Nat → Nat → Nat) (l : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => A (Nat.sub k 1) x) (fun k => AI k x) l

@[expose] noncomputable def wAp (A AI : Nat → Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ ih => strictN ih (fun v => lAp A AI l v)) w

@[expose] noncomputable def wApI (A AI : Nat → Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun l _ ih y => strictN (lAp AI A l y) ih) w x

@[expose] noncomputable def pkA (G : Nat → Nat) (k x : Nat) : Nat := apP (G k) x

@[expose] noncomputable def itF (f : Nat → Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih f) k

@[expose] noncomputable def mImg (P : Nat → Nat) (o r m : Nat) : Nat := img4 (mAp P o r m)

@[expose] noncomputable def inSp (P : Nat → Nat) (o r u : Nat) : Bool :=
  anyK (Nat.shiftLeft (nat_lit 1) r) (fun m => Nat.beq (mImg P o r m) u)

@[expose] noncomputable def ebB (P : Nat → Nat) (o r : Nat) : Bool :=
  bAnd(allN r (fun i => strictB (P (Nat.add o i)) (fun a =>
      bAnd(allN (nat_lit 4) (fun b => Nat.beq (apP a (apP a b)) b),
        allN r (fun j => strictB (P (Nat.add o j)) (fun c =>
          allN (nat_lit 4) (fun b => Nat.beq (apP a (apP c b)) (apP c (apP a b)))))))),
    allN (Nat.sub (Nat.shiftLeft (nat_lit 1) r) (nat_lit 1)) (fun m =>
      bIf(allN (nat_lit 4) (fun b => Nat.beq (mAp P o r (Nat.succ m) b) b), false, true)))

@[expose] noncomputable def normB (P : Nat → Nat) (o r : Nat) (A AI : Nat → Nat) : Bool :=
  allN r (fun i => strictB (P (Nat.add o i)) (fun v =>
    inSp P o r (img4 (fun x => A (apP v (AI x))))))

@[expose] noncomputable def ordB (f : Nat → Nat) (p : Nat) : Bool :=
  bAnd(allN (nat_lit 4) (fun b => Nat.beq (itF f p b) b),
    bIf(allN (nat_lit 4) (fun b => Nat.beq (f b) b), false, true))

@[expose] noncomputable def fixC (f : Nat → Nat) : Nat :=
  foldN (nat_lit 4060) (fun x c => nIf(Nat.beq (f x) x, Nat.succ c, c)) (nat_lit 0)

@[expose] noncomputable def commF (a ai b bi : Nat → Nat) (x : Nat) : Nat := a (b (ai (bi x)))

end CFSG.KC.Misc.RuBigZ

end
