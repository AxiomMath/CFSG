module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def eG (p i : Nat) : Nat := pg (nat_lit 6) (nat_lit 63) p i

@[expose] noncomputable def eC (p q : Nat) : Nat := pcomp (nat_lit 32) (nat_lit 6) (nat_lit 63) p q

@[expose] noncomputable def eId : Nat := pidn (nat_lit 32) (nat_lit 6)

@[expose] noncomputable def eCanon (p : Nat) : Bool :=
  canonK (nat_lit 32) (nat_lit 6) (nat_lit 63) (nat_lit 192) p

@[expose] noncomputable def eMul (ET : Nat → Nat) (a b : Nat) : Nat := eG (ET a) b

@[expose] noncomputable def eTabK (ET : Nat → Nat) (mul : Nat → Nat → Nat) : Bool :=
  allN (nat_lit 32) (fun a => bAnd(eCanon (ET a),
    allN (nat_lit 32) (fun b => Nat.beq (eMul ET a b) (mul a b))))

@[expose] noncomputable def eAutK (ET : Nat → Nat) (p q : Nat) : Bool :=
  bAnd(permOK (nat_lit 32) (nat_lit 6) (nat_lit 63) (nat_lit 192) p q,
    allN (nat_lit 32) (fun a => strictB (eG p a) (fun pa =>
      allN (nat_lit 32) (fun b =>
        Nat.beq (eG p (eMul ET a b)) (eMul ET pa (eG p b))))))

@[expose] noncomputable def eInvK (p : Nat) : Bool :=
  bAnd(sqIdK (nat_lit 32) (nat_lit 6) (nat_lit 63) (nat_lit 192) eId p,
    bIf(Nat.beq p eId, false, true))

@[expose] noncomputable def eRecHdK (ET G GI : Nat → Nat) (k cnt : Nat) (T PL : Nat → Nat) : Bool :=
  bAnd(szOK (nat_lit 32) (nat_lit 6), bAnd(idK (nat_lit 32) (nat_lit 6) (nat_lit 63),
    bAnd(allN k (fun j => eAutK ET (G j) (GI j)),
      penumHdK eId cnt cnt T PL)))

@[expose] noncomputable def eRecSlK (G : Nat → Nat) (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat)
    (lo len : Nat) : Bool :=
  penumSlK (nat_lit 32) (nat_lit 6) (nat_lit 63) (nat_lit 192) false G G k cnt T PL POS SRT SRI lo len

@[expose] noncomputable def eSylHdK (cnt : Nat) (T SP : Nat → Nat) (kS cntS : Nat)
    (ST SPL : Nat → Nat) : Bool :=
  bAnd(allN kS (fun j => Nat.blt (SP j) cnt), penumHdK eId cntS cntS ST SPL)

@[expose] noncomputable def eInvCount (T : Nat → Nat) (c : Nat) : Nat :=
  foldUp c (fun i acc => nIf(eInvK (T i), Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def eClsK (cnt : Nat) (T : Nat → Nat) (nr : Nat) (REP : Nat → Nat) (nv : Nat)
    (IV ICL ICJ : Nat → Nat) : Bool :=
  bAnd(allN nr (fun r => strictB (REP r) (fun x => bAnd(Nat.blt x cnt, eInvK (T x)))),
  bAnd(Nat.beq (eInvCount T cnt) nv,
    allN nv (fun q => strictB (IV q) (fun v => strictB (ICL q) (fun l => strictB (ICJ q) (fun c =>
      bAnd(Nat.blt v cnt, bAnd(Nat.blt l nr, bAnd(Nat.blt c cnt, bAnd(eInvK (T v),
      bAnd(bIf(Nat.blt (Nat.succ q) nv, Nat.blt v (IV (Nat.succ q)), true),
        strictB (T c) (fun g => Nat.beq (eC g (T (REP l))) (eC (T v) g)))))))))))))

@[expose] noncomputable def eKind (ET : Nat → Nat) (s k : Nat) : Bool :=
  bAnd(Nat.beq (eMul ET k k) s, bIf(Nat.beq k (nat_lit 0), false, bIf(Nat.beq k (nat_lit 21), false, true)))

@[expose] noncomputable def eSqHit (p c k : Nat) : Bool := Nat.beq (eG p (eG p c)) k

@[expose] noncomputable def eSqK (ET : Nat → Nat) (cnt : Nat) (T : Nat → Nat) (s c : Nat) (W : Nat → Nat) :
    Bool :=
  bAnd(eKind ET s c, bAnd(allN c (fun k => bIf(eKind ET s k, false, true)),
    allN (nat_lit 32) (fun k => bIf(eKind ET s k,
      strictB (W k) (fun i => bAnd(Nat.blt i cnt, eSqHit (T i) c k)), true))))

@[expose] noncomputable def eAnti (ET : Nat → Nat) (a b : Nat) : Bool :=
  bAnd(eKind ET (nat_lit 0) a, bAnd(eKind ET (nat_lit 0) b,
    bIf(Nat.beq (eMul ET a b) (eMul ET b a), false, true)))

@[expose] noncomputable def eAntiCount (ET : Nat → Nat) : Nat :=
  foldUp (nat_lit 1024) (fun x acc =>
    nIf(eAnti ET (Nat.shiftRight x (nat_lit 5)) (Nat.land x (nat_lit 31)), Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def ePairK (ET : Nat → Nat) (cnt : Nat) (T : Nat → Nat) (np : Nat)
    (PA PB PI : Nat → Nat) : Bool :=
  bAnd(Nat.beq (eAntiCount ET) np,
    allN np (fun q => strictB (PA q) (fun a => strictB (PB q) (fun b => strictB (PI q) (fun i =>
      bAnd(Nat.blt a (nat_lit 32), bAnd(Nat.blt b (nat_lit 32), bAnd(eAnti ET a b,
      bAnd(bIf(Nat.blt (Nat.succ q) np,
        Nat.blt (Nat.add (Nat.mul (nat_lit 32) a) b)
          (Nat.add (Nat.mul (nat_lit 32) (PA (Nat.succ q))) (PB (Nat.succ q))), true),
      bAnd(Nat.blt i cnt, strictB (T i) (fun p =>
        bAnd(eSqHit p (PA (nat_lit 0)) a, eSqHit p (PB (nat_lit 0)) b))))))))))))

@[expose] noncomputable def eInnK (ET : Nat → Nat) (cnt : Nat) (T : Nat → Nat) (ni : Nat)
    (INN INE : Nat → Nat) : Bool :=
  allN ni (fun u => strictB (INN u) (fun i => strictB (INE u) (fun e =>
    bAnd(Nat.blt i cnt, bAnd(Nat.blt e (nat_lit 32),
    bAnd(bIf(Nat.blt (Nat.succ u) ni, Nat.blt i (INN (Nat.succ u)), true),
      strictB (T i) (fun p => allN (nat_lit 32) (fun x =>
        Nat.beq (eMul ET (eG p x) e) (eMul ET e x)))))))))

@[expose] noncomputable def eQK (cnt : Nat) (T : Nat → Nat) (ni : Nat) (INN QC : Nat → Nat) : Bool :=
  allN ni (fun u => allN ni (fun v => strictB (QC (Nat.add (Nat.mul ni u) v)) (fun c =>
    bAnd(Nat.blt c cnt, bAnd(allN ni (fun u' => bIf(Nat.beq c (INN u'), false, true)),
      strictB (T c) (fun g => bAnd(eInvK g,
      bAnd(strictB (T (INN u)) (fun a => Nat.beq (eC g a) (eC a g)),
        strictB (T (INN v)) (fun b => Nat.beq (eC g b) (eC b g))))))))))

end CFSG.KS.EAut

end
