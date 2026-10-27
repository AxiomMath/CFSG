module

public import Certificates.Data.Kernel.Fi22.Letters
public import Certificates.Data.Kernel.Fi22.T46
public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.KS.Fi22Cent

open CFSG.KC.Enum CFSG.KS.Fi22L CFSG.KS.T46K CFSG.F4.Native

@[expose] def centText : String := include_str "cent.hex"

@[expose] noncomputable def centP : Nat := by hex_nat centText 84256 1617121518949697302

@[expose] noncomputable def cT (t : Nat) : Nat :=
  Nat.land (Nat.shiftRight centP (Nat.mul (nat_lit 42120) t)) Fi22L.tM

@[expose] noncomputable def EAK (x : Nat) : Nat := lk (cT (nat_lit 0)) x
@[expose] noncomputable def EPK (x : Nat) : Nat := lk (cT (nat_lit 1)) x
@[expose] noncomputable def PHK (x : Nat) : Nat := lk (cT (nat_lit 2)) x
@[expose] noncomputable def PIK (x : Nat) : Nat := lk (cT (nat_lit 3)) x
@[expose] noncomputable def ORK (x : Nat) : Nat := lk (cT (nat_lit 4)) x
@[expose] noncomputable def OIK (x : Nat) : Nat := lk (cT (nat_lit 5)) x
@[expose] noncomputable def TPK (x : Nat) : Nat := lk (cT (nat_lit 6)) x
@[expose] noncomputable def TGK (x : Nat) : Nat := lk (cT (nat_lit 7)) x
@[expose] noncomputable def GSK (x : Nat) : Nat := lk (cT (nat_lit 8)) x

@[expose] noncomputable def gA (y : Nat) : Nat := lk (orbT (nat_lit 0)) y
@[expose] noncomputable def gB (y : Nat) : Nat := lk (orbT (nat_lit 1)) y
@[expose] noncomputable def gBi (y : Nat) : Nat := reg ljPacked (nat_lit 2) y
@[expose] noncomputable def parK (k : Nat) : Nat := lk (orbT (nat_lit 2)) k
@[expose] noncomputable def labK (k : Nat) : Nat := lk (orbT (nat_lit 3)) k

@[expose] noncomputable def uInvF (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      ih (parK k) (nIf(Nat.beq (labK k) (nat_lit 1), gA x, gBi x)))) f

@[expose] noncomputable def uF (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun _ ih k y => nIf(Nat.beq k (nat_lit 0), y,
      strictN (ih (parK k) y) fun z => nIf(Nat.beq (labK k) (nat_lit 1), gA z, gB z))) f

@[expose] noncomputable def cK (k x : Nat) : Nat :=
  uF (nat_lit 3510) k (strictN (uInvF (nat_lit 3510) k x) gA)

@[expose] noncomputable def eaK : Bool :=
  bAnd(allN (nat_lit 693) fun i => strictB (EAK i) fun k =>
      bAnd(Nat.blt (nat_lit 0) k, bAnd(Nat.blt k (nat_lit 3510), bAnd(Nat.beq (gA k) k,
        Nat.beq (EPK k) i))),
    allN (nat_lit 692) fun i => Nat.blt (EAK i) (EAK (Nat.succ i)))

@[expose] noncomputable def epK : Bool :=
  allN (nat_lit 3510) fun x => strictB (EPK x) fun m =>
    bIf(Nat.blt m (nat_lit 693), Nat.beq (EAK m) x,
      bAnd(Nat.beq m (nat_lit 693), bIf(Nat.beq x (nat_lit 0), true, Bool.not (Nat.beq (gA x) x))))

@[expose] noncomputable def phiK : Bool :=
  allN (nat_lit 693) fun i => bAnd(Nat.blt (PHK i) (nat_lit 693), bAnd(Nat.blt (PIK i) (nat_lit 693),
    bAnd(Nat.beq (PIK (PHK i)) i, Nat.beq (PHK (PIK i)) i)))

@[expose] noncomputable def rowAt (s j : Nat) : Bool :=
  strictB (GSK s) fun r => strictB (cK (EAK r) (EAK j)) fun x => strictB (EPK x) fun m =>
    bAnd(Nat.blt r (nat_lit 693), bAnd(Nat.blt m (nat_lit 693), bAnd(Nat.beq (EAK m) x,
      Nat.beq (UC (PHK m)) (normC (tvC (UC (PHK r)) (UC (PHK j)))))))

@[expose] noncomputable def rowSl (s : Nat) : Bool := allN (nat_lit 693) (rowAt s)

@[expose] noncomputable def treeK : Bool :=
  bAnd(Nat.beq (ORK (nat_lit 0)) (GSK (nat_lit 0)),
  bAnd(allN (nat_lit 693) fun t => bAnd(Nat.blt (ORK t) (nat_lit 693), bIf(Nat.beq t (nat_lit 0), true,
      strictB (TPK t) fun s => strictB (TGK t) fun g => bAnd(Nat.blt s t, bAnd(Nat.blt g (nat_lit 6),
        Nat.beq (cK (EAK (GSK g)) (EAK (ORK s))) (EAK (ORK t)))))),
    allN (nat_lit 693) fun i => bAnd(Nat.blt (OIK i) (nat_lit 693), Nat.beq (ORK (OIK i)) i)))

@[expose] noncomputable def itK (f : Nat → Nat) (m : Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun _ ih x => strictN (f x) ih) m x
@[expose] noncomputable def wordK (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun k _ ih => cK k ih) w

@[expose] noncomputable def powK (w : List Nat) (m : Nat) (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(Nat.beq (itK (wordK w) m q) (gA q), ih)) Q

end CFSG.KS.Fi22Cent

end
