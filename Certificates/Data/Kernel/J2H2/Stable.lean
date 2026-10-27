module

public import Certificates.Data.Kernel.J2H2.Defs

public section

namespace CFSG.KD.J2H2

open CFSG.KC.Enum

@[expose] noncomputable def lbeq (L M : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun a _ ih M => List.rec (motive := fun _ => Bool) false (fun b M' _ => bAnd(Nat.beq a b, ih M')) M)
    L M

@[expose] noncomputable def wordK (A B : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 315 9)
    (fun k _ ih => pcomp 315 9 511 (nIf(Nat.beq k 0, A, B)) ih) w

@[expose] noncomputable def conjL (E : Nat → Nat) (g : Nat) (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(Nat.blt e 16384,
      bAnd(Nat.beq (pcomp 315 9 511 g (E (Nat.land e 127))) (pcomp 315 9 511 (E (Nat.shiftRight e 7)) g),
        ih))) Q

@[expose] noncomputable def conjK (A B : Nat) (E : Nat → Nat) (CW : List (List Nat)) (CQ : List (List Nat)) :
    Bool :=
  allN 5 (fun l => strictB (wordK A B (getL [] CW l)) (fun g => conjL E g (getL [] CQ l)))

@[expose] noncomputable def matWordInvK (AI BI : List Nat) (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun j _ ih acc => ih (matMulK (Bool.rec (motive := fun _ => List Nat) BI AI (Nat.beq j 0)) acc)) w id12

@[expose] noncomputable def rgK (AI BI : List Nat) (CW RGI : List (List Nat)) : Bool :=
  allN 5 (fun l => lbeq (getL [] RGI l) (matWordInvK AI BI (getL [] CW l)))

@[expose] noncomputable def spgK (RGI SPG : List (List Nat)) : Bool :=
  allN 5 (fun l => spRowK (getL [] SPG l) (getL [] RGI l))

@[expose] noncomputable def packM (P : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.lor c (Nat.shiftLeft ih 12)) P

@[expose] noncomputable def mvP (Y v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c ih => Nat.xor ih (Nat.mul fld(v, c, 1) fld(Y, Nat.mul 12 c, 4095))) 12

@[expose] noncomputable def mulMP (Y R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun c ih => Nat.lor ih (Nat.shiftLeft (mvP Y fld(R, Nat.mul 12 c, 4095)) (Nat.mul 12 c))) 12

@[expose] noncomputable def rsK (RS : List Nat) (GP PP : Nat) (A B : List Nat) (yW : List (List Nat)) :
    Bool :=
  bAnd(Nat.beq (getL 0 RS 0) (packM id12), allN 3 (fun k =>
    strictB (packM (matWordK A B (getL [] yW k))) (fun Y => allN 127 (fun i =>
      bIf(Nat.beq (pg 2 3 GP (Nat.succ i)) k,
        Nat.beq (getL 0 RS (Nat.succ i)) (mulMP Y (getL 0 RS (pg 7 127 PP (Nat.succ i)))), true)))))

@[expose] noncomputable def par12 (x : Nat) : Nat :=
  (fun p => fld(150, Nat.land (Nat.xor p (Nat.shiftRight p 3)) 7, 1)) (Nat.xor x (Nat.shiftRight x 6))

@[expose] noncomputable def rT (R μ : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun r ih => Nat.lor ih (Nat.shiftLeft (par12 (Nat.land fld(R, Nat.mul 12 r, 4095) μ)) r)) 12

@[expose] noncomputable def contrib (μ D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun r ih => Nat.xor ih (nIf(Nat.beq fld(μ, r, 1) 1, fld(D, Nat.mul 32 r, 1073741823), 0))) 12

@[expose] noncomputable def offL (NL : List Nat) (l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.add ih (getL 0 NL i)) l

@[expose] noncomputable def phiCell (sp : List Nat) (n o Mu b rowS rowP t pt : Nat) : Nat :=
  (fun D => Nat.rec (motive := fun _ => Nat) 0 (fun m ih => Nat.xor ih
      (Nat.shiftLeft (contrib fld(Mu, Nat.mul 12 (Nat.add (Nat.mul n b) m), 4095) D) (Nat.mul 32 (Nat.add o m)))) n)
    (Nat.xor (fieldAt rowS t) (mulRowK sp (fieldAt rowP pt) 1073741823))

@[expose] noncomputable def uCell (MTP n o Mu b s R t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun m ih =>
    (fun μ q0 => Nat.xor ih (Nat.xor (Nat.shiftLeft (rT R μ) (Nat.mul 12 (Nat.add q0 t)))
      (Nat.xor (Nat.shiftLeft μ (Nat.mul 12 (Nat.add q0 (pg 7 127 MTP (Nat.add (Nat.mul 128 s) t)))))
        (Nat.shiftLeft μ (Nat.mul 12 (Nat.add q0 s))))))
      fld(Mu, Nat.mul 12 (Nat.add (Nat.mul n b) m), 4095) (Nat.mul 128 (Nat.add o m))) n

@[expose] noncomputable def xorL (f : Nat → Nat → Nat) (Q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun e _ ih b => Nat.xor (f b e) (ih (Nat.succ b))) Q 0

@[expose] noncomputable def phiAcc (HP : Nat) (CQ PHI SPG : List (List Nat)) (NL : List Nat) (l : Nat) : Nat :=
  (fun Q P sp n o => xorL (fun a e => strictN (rowAt HP (Nat.land e 127)) (fun rowS =>
      strictN (rowAt HP (Nat.shiftRight e 7)) (fun rowP =>
        xorL (fun b e' => phiCell sp n o (getL 0 P a) b rowS rowP (Nat.land e' 127) (Nat.shiftRight e' 7)) Q)))
    Q) (getL [] CQ l) (getL [] PHI l) (getL [] SPG l) (getL 0 NL l) (offL NL l)

@[expose] noncomputable def uAcc (MTP : Nat) (RS : List Nat) (CQ PHI : List (List Nat)) (NL : List Nat)
    (l : Nat) : Nat :=
  (fun Q P n o => xorL (fun a e => (fun s => strictN (getL 0 RS s) (fun R =>
      xorL (fun b e' => uCell MTP n o (getL 0 P a) b s R (Nat.land e' 127)) Q)) (Nat.land e 127))
    Q) (getL [] CQ l) (getL [] PHI l) (getL 0 NL l) (offL NL l)

@[expose] noncomputable def phiK (MTP : Nat) (RS : List Nat) (CQ PHI : List (List Nat)) (NL : List Nat)
    (l : Nat) : Bool :=
  Nat.beq (uAcc MTP RS CQ PHI NL l) 0

@[expose] noncomputable def phvK (HP : Nat) (CQ PHI SPG : List (List Nat)) (NL : List Nat) (PHV : Nat) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun l ih => Nat.xor ih (phiAcc HP CQ PHI SPG NL l)) 5) PHV

@[expose] noncomputable def bitsL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => Nat.lor (Nat.shiftLeft 1 i) ih) L

@[expose] noncomputable def selX (R PHV : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun m ih => Nat.xor ih (Nat.mul fld(R, m, 1) fld(PHV, Nat.mul 32 m, 1073741823))) 10

@[expose] noncomputable def rankK (PHV : Nat) (IND RINV : List Nat) : Bool :=
  bAnd(Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) IND) 10,
    allN 10 (fun i => Nat.beq (Nat.land (selX (getL 0 RINV i) PHV) (bitsL IND)) (Nat.shiftLeft 1 (getL 0 IND i))))

@[expose] noncomputable def depBits (DEPA : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun e _ ih => Nat.lor (Nat.shiftLeft 1 (Nat.land e 31)) ih) DEPA

@[expose] noncomputable def mixOne (A Q L0 : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i ih => Nat.xor ih (nIf(Nat.beq fld(A, i, 1) 1, Nat.land (Nat.shiftRight Q i) L0, 0))) 30

@[expose] noncomputable def mixK (DEPA : List Nat) (Q L0 : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => Nat.xor ih (Nat.shiftLeft (mixOne (Nat.shiftRight e 5) Q L0) (Nat.land e 31))) DEPA

@[expose] noncomputable def permF (V T o : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun h ih => Nat.lor ih (Nat.shiftLeft (fieldAt V (pg 7 127 T (Nat.add o h))) (Nat.mul 384 h))) 128

@[expose] noncomputable def relK (HP REP LMP BR : Nat) (SP : List (List Nat)) (DEPA : List Nat) (k : Nat) :
    Bool :=
  (fun Q L0 => Nat.beq (Nat.land Q (Nat.mul L0 (depBits DEPA)))
      (Nat.xor (mixK DEPA Q L0) (Nat.xor (Nat.xor (mulRowK (getL [] SP k) BR (Nat.mul REP 1073741823))
        (permF BR LMP (Nat.mul 128 k))) (Nat.mul (fieldAt BR (Nat.succ k)) REP))))
    (rowAt HP (Nat.succ k)) (Nat.mul REP (spread 4095))

@[expose] noncomputable def covK (IND DEPA : List Nat) (BR : Nat) : Bool :=
  bAnd(Nat.beq (Nat.land (bitsL IND) (depBits DEPA)) 0,
    bAnd(Nat.beq (Nat.lor (bitsL IND) (depBits DEPA)) 1073741823,
      bAnd(Nat.beq (fieldAt BR 0) 0,
        List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(Nat.blt (Nat.land e 31) 30,
          bAnd(Nat.beq (Nat.land (Nat.shiftRight e 5) (bitsL IND)) (Nat.shiftRight e 5), ih))) DEPA)))

end CFSG.KD.J2H2

end
