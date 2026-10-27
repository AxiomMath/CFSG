module

public import Certificates.Data.Kernel.SporSch.PairCl

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def lptK (w NR : Nat) (LT : Nat → Nat) (l x : Nat) : Nat :=
  fld(LT (Nat.add (Nat.mul l NR) (Nat.shiftRight x (nat_lit 6))), Nat.mul w (Nat.land x (nat_lit 63)),
    mask w)

@[expose] noncomputable def lvT (NL fw : Nat) (T : Nat → Nat) (i k : Nat) : Nat :=
  fld(T (Nat.add (Nat.mul i NL) (Nat.shiftRight k (nat_lit 6))), Nat.mul fw (Nat.land k (nat_lit 63)),
    mask fw)

@[expose] noncomputable def invL (kS l : Nat) : Nat := nIf(Nat.blt l kS, Nat.add l kS, Nat.sub l kS)

@[expose] noncomputable def trPtT (w NR NL : Nat) (LT PT : Nat → Nat) (i k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      strictN (lvT NL (nat_lit 24) PT i k) (fun e =>
      strictN (ih (Nat.land e (nat_lit 65535)) x) (fun y =>
        lptK w NR LT (Nat.shiftRight e (nat_lit 16)) y))))
    k k x

@[expose] noncomputable def trInvPtT (w kS NR NL : Nat) (LT PT : Nat → Nat) (i k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      strictN (lvT NL (nat_lit 24) PT i k) (fun e =>
      strictN (lptK w NR LT (invL kS (Nat.shiftRight e (nat_lit 16))) x) (fun y =>
        ih (Nat.land e (nat_lit 65535)) y))))
    k k x

@[expose] noncomputable def nfPtT (w NR NL : Nat) (LT PT : Nat → Nat) (nb NF x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => strictN (trPtT w NR NL LT PT i fld(NF, Nat.mul (nat_lit 16) i, nat_lit 65535) x) ih)
    nb x

@[expose] noncomputable def nfKeyT (n w NR NL : Nat) (LT PT : Nat → Nat) (nb : Nat) (bs : List Nat)
    (NF : Nat) : Nat :=
  keyL n (nfPtT w NR NL LT PT nb NF) bs

@[expose] noncomputable def conjKeyT (n w kS NR NL : Nat) (LT PT : Nat → Nat) (nb : Nat)
    (bs : List Nat) (l NF : Nat) : Nat :=
  keyL n (fun b => lptK w NR LT l (nfPtT w NR NL LT PT nb NF (lptK w NR LT (invL kS l) b))) bs

@[expose] noncomputable def siftNFT (n w kS NR NL : Nat) (LT PT QT : Nat → Nat) (nb K : Nat) : Nat :=
  (Nat.rec (motive := fun _ => (Nat → Nat) → Nat × Nat)
    (fun _ => (nat_lit 0, nat_lit 0))
    (fun i ih cur => (fun k =>
      Prod.rec (motive := fun _ => Nat × Nat) (fun acc _ =>
        (Nat.lor acc (Nat.shiftLeft k (Nat.mul (nat_lit 16) (Nat.sub (Nat.sub nb (nat_lit 1)) i))), k))
        (ih (fun t => trInvPtT w kS NR NL LT PT (Nat.sub (Nat.sub nb (nat_lit 1)) i) k (cur t))))
      (lvT NL w QT (Nat.sub (Nat.sub nb (nat_lit 1)) i) (cur (Nat.sub (Nat.sub nb (nat_lit 1)) i))))
    nb (keyAt n K)).1

@[expose] noncomputable def stepNFT (n w kS NR NL : Nat) (LT PT QT : Nat → Nat) (nb : Nat)
    (bs : List Nat) (GL X W K : Nat → Nat) (c h l cur : Nat) : Nat :=
  nIf(Nat.blt h cur,
    strictN (conjKeyT n w kS NR NL LT PT nb bs (GL l) (nfX nb (X h))) (fun kz =>
    strictN fld(W h, Nat.mul (nat_lit 20) l, nat_lit 1048575) (fun j =>
      nIf(bAnd(Nat.blt j cur, Nat.beq (K j) kz), cur,
      nIf(bAnd(Nat.beq j cur, bAnd(Nat.beq (K j) kz, strictB (X j) (fun xj =>
          bAnd(Nat.beq (nfX nb xj) (siftNFT n w kS NR NL LT PT QT nb kz),
          bAnd(Nat.beq (parNF nb xj) h, Nat.beq (labNF nb xj) l))))),
        Nat.succ cur, failC)))),
    nIf(Nat.beq cur c, cur, failC))

@[expose] noncomputable def runNFT (n w kS NR NL : Nat) (LT PT QT : Nat → Nat) (nb : Nat)
    (bs : List Nat) (GL X W K : Nat → Nat) (kg c : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (foldUp kg (fun l cur =>
      stepNFT n w kS NR NL LT PT QT nb bs GL X W K c h l cur) cur)
      (fun c' => strictN (Nat.succ h) (fun h' => ih h' c')))

@[expose] noncomputable def startNFT (n w kS NR NL : Nat) (LT PT QT : Nat → Nat) (nb K₀ x : Nat) :
    Bool :=
  bAnd(Nat.beq (nfX nb x) (siftNFT n w kS NR NL LT PT QT nb K₀),
    bAnd(Nat.beq (parNF nb x) (nat_lit 0), Nat.beq (labNF nb x) (nat_lit 0)))

@[expose] noncomputable def recOKT (n w NR NL : Nat) (LT PT : Nat → Nat) (nb : Nat) (bs : List Nat)
    (cnt X K : Nat → Nat) (c i : Nat) : Bool :=
  bIf(Nat.blt i c, strictB (nfX nb (X i)) (fun x => bAnd(allN nb (fun t =>
    Nat.blt fld(x, Nat.mul (nat_lit 16) t, nat_lit 65535) (cnt t)),
    Nat.beq (K i) (nfKeyT n w NR NL LT PT nb bs x))), true)

@[expose] noncomputable def ltOKT (n w kS NR : Nat) (S SI LT : Nat → Nat) (j : Nat) : Bool :=
  bIf(Nat.blt j (Nat.mul (Nat.add kS kS) n), strictB (Nat.div j n) (fun l => strictB (Nat.mod j n) (fun x =>
    Nat.beq (lptK w NR LT l x) (pg w (mask w) (letterK S SI kS l) x))), true)

@[expose] noncomputable def ptOKT (n w NL : Nat) (LR Ts PT : Nat → Nat) (i k : Nat) : Bool :=
  strictB (LR i) (fun R => bIf(Nat.blt k (rcnt R),
    Nat.beq (lvT NL (nat_lit 24) PT i k) (Nat.add (rpar w (mask w) (Nat.mul n w) R k)
      (Nat.shiftLeft (stAt (Ts i) (rlab n (Nat.mul n w) R k)) (nat_lit 16))), true))

@[expose] noncomputable def qtOKT (n w NL : Nat) (LR QT : Nat → Nat) (i z : Nat) : Bool :=
  bIf(Nat.blt z n, Nat.beq (lvT NL w QT i z) (rpos w (mask w) (Nat.mul n w) (LR i) z), true)

end CFSG.KS.SporSch

end
