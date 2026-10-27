module

public import CFSG.Certificates.Kernel.J4.KShape.Shape

public section

namespace CFSG.KJ4.R

open CFSG.KJ4 CFSG.KJ4.S CFSG.KC.Loop

@[expose] noncomputable def bsel {α : Type} (c : Bool) (t e : α) : α := Bool.rec (motive := fun _ => α) e t c

@[expose] def m16 : Nat := nat_lit 65535

@[expose] def mPay : Nat := nat_lit 521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728255

@[expose] noncomputable def f16 (p o : Nat) : Nat := Nat.land (Nat.shiftRight p o) m16

structure KD where
  FT : Nat → Nat
  HT : Nat → Nat
  WT : Nat → Nat
  RT : Nat → Nat
  RZT : Nat → Nat
  PT : Nat → Nat
  OT : Nat → Nat
  CT : Nat → Nat
  LT : Nat → Nat
  EK : Nat → Nat
  EN : Nat → Nat
  ET0 : Nat → Nat
  ET : Nat → Nat
  INV : Nat
  TH : Nat
  LET : Nat
  TR1 : Nat
  PS1 : Nat
  W0 : Nat
  PAW : Nat
  PBW : Nat
  W0W : Nat
  ND : Nat
  NOM : Nat
  NF : Nat
  nH : Nat
  i0 : Nat
  hx : Nat
  hw : Nat
  sw : Nat
  sn : Nat
  cv : Nat
  neK : Nat
  neN : Nat
  neT0 : Nat
  neT : Nat
  LVK : List Nat
  LVN : List Nat
  LVT0 : List Nat
  LVT : List Nat
  BK : Nat
  BN : Nat
  BT : Nat
  BT0 : Nat
  DCH : List ((Nat → Nat) × (Nat × (List Nat × Nat)))
  WREC : Nat
  CM : Nat

structure MD where
  FT : Nat → Nat
  HT : Nat → Nat
  WT : Nat → Nat
  OT : Nat → Nat
  SG : Nat → Nat
  TW : Nat → Nat
  ND : Nat
  NOM : Nat
  NF : Nat
  nH : Nat
  nSG : Nat
  nW : Nat
  ZW : Nat

@[expose] noncomputable def kFail : Nat × St := Prod.mk (Nat.mul (nat_lit 2) FAIL) bad
@[expose] noncomputable def mFail : Nat × St4 := Prod.mk (Nat.mul (nat_lit 2) FAIL) bad4

@[expose] noncomputable def wK (c : Nat) : Nat :=
  bsel (orB (Nat.beq c (nat_lit 1)) (Nat.beq c (nat_lit 2))) (nat_lit 17)
    (bsel (orB (Nat.beq c (nat_lit 3)) (Nat.beq c (nat_lit 4))) (nat_lit 180)
      (bsel (Nat.beq c (nat_lit 5)) (nat_lit 64) (bsel (Nat.beq c (nat_lit 8)) (nat_lit 32) (nat_lit 0))))

@[expose] noncomputable def wM (c : Nat) : Nat :=
  bsel (Nat.beq c (nat_lit 0)) (nat_lit 16)
    (bsel (orB (Nat.beq c (nat_lit 1)) (Nat.beq c (nat_lit 2))) (nat_lit 17)
      (bsel (Nat.beq c (nat_lit 3)) (nat_lit 164) (bsel (Nat.beq c (nat_lit 4)) (nat_lit 308)
        (bsel (Nat.beq c (nat_lit 5)) (nat_lit 64) (bsel (Nat.beq c (nat_lit 8)) (nat_lit 32) (nat_lit 0))))))

@[expose] noncomputable def kStep (k : KD) (c p : Nat) (q : Nat × St) : Nat × St :=
  Prod.rec (motive := fun _ => Nat × St) (fun m s =>
    bsel (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 0))
      (bsel (Nat.beq c (nat_lit 5))
        (Prod.mk (nat_lit 1) (stS k.FT k.HT k.WT k.ND k.NOM (f16 p (nat_lit 0)) (f16 p (nat_lit 16))
          (f16 p (nat_lit 32)) (f16 p (nat_lit 48)) (Nat.shiftRight m (nat_lit 1))))
      (bsel (Nat.beq c (nat_lit 7))
        (Prod.mk (Nat.mul (nat_lit 2) (jTree k.FT false k.ND k.NOM (Nat.shiftRight m (nat_lit 1)))) bad)
      (bsel (Nat.beq c (nat_lit 8))
        (Prod.mk (Nat.mul (nat_lit 2) (jAx k.FT k.HT false k.ND k.NOM (f16 p (nat_lit 0)) (f16 p (nat_lit 16))
          (Nat.shiftRight m (nat_lit 1)))) bad)
        kFail)))
      (bsel (Nat.beq c (nat_lit 0)) (Prod.mk (nat_lit 1) (sNs k.LET s))
      (bsel (Nat.beq c (nat_lit 1)) (Prod.mk (nat_lit 1) (sEfs k.FT (Nat.land p (nat_lit 1)) (f16 p (nat_lit 1)) s))
      (bsel (Nat.beq c (nat_lit 2)) (Prod.mk (nat_lit 1) (sEbs k.FT (Nat.land p (nat_lit 1)) (f16 p (nat_lit 1)) s))
      (bsel (Nat.beq c (nat_lit 3)) (Prod.mk (nat_lit 1) (sUfs k.FT k.OT k.LT k.TH (Nat.land p (nat_lit 1))
          (f16 p (nat_lit 1)) (f16 p (nat_lit 17)) (Nat.land (Nat.shiftRight p (nat_lit 33)) (nat_lit 7))
          (Nat.land (Nat.shiftRight p (nat_lit 36)) mask144) s))
      (bsel (Nat.beq c (nat_lit 4)) (Prod.mk (nat_lit 1) (sUbs k.FT k.OT k.LT k.TH (Nat.land p (nat_lit 1))
          (f16 p (nat_lit 1)) (f16 p (nat_lit 17)) (Nat.land (Nat.shiftRight p (nat_lit 33)) (nat_lit 7))
          (Nat.land (Nat.shiftRight p (nat_lit 36)) mask144) s))
      (bsel (Nat.beq c (nat_lit 6)) (Prod.mk (Nat.mul (nat_lit 2) (wEndJ s)) bad)
        kFail))))))) q

@[expose] noncomputable def mStep (d : MD) (k : KD) (tr : Bool) (c p : Nat) (q : Nat × St4) : Nat × St4 :=
  Prod.rec (motive := fun _ => Nat × St4) (fun m s =>
    bsel (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 0))
      (bsel tr
        (bsel (Nat.beq c (nat_lit 9)) (Prod.mk (nat_lit 1) (stTr d.TW d.NF (Nat.shiftRight m (nat_lit 1)))) mFail)
        (bsel (Nat.beq c (nat_lit 5))
          (Prod.mk (nat_lit 1) (stSm d.FT d.HT d.WT d.ND d.NOM (f16 p (nat_lit 0)) (f16 p (nat_lit 16))
            (f16 p (nat_lit 32)) (f16 p (nat_lit 48)) (Nat.shiftRight m (nat_lit 1))))
        (bsel (Nat.beq c (nat_lit 7))
          (Prod.mk (Nat.mul (nat_lit 2) (jTree d.FT true d.ND d.NOM (Nat.shiftRight m (nat_lit 1)))) bad4)
        (bsel (Nat.beq c (nat_lit 8))
          (Prod.mk (Nat.mul (nat_lit 2) (jAx d.FT d.HT true d.ND d.NOM (f16 p (nat_lit 0)) (f16 p (nat_lit 16))
            (Nat.shiftRight m (nat_lit 1)))) bad4)
          mFail))))
      (bsel (Nat.beq c (nat_lit 0)) (Prod.mk (nat_lit 1) (mNs d.SG (f16 p (nat_lit 0)) s))
      (bsel (Nat.beq c (nat_lit 1)) (Prod.mk (nat_lit 1) (mEfs d.FT (Nat.land p (nat_lit 1)) (f16 p (nat_lit 1)) s))
      (bsel (Nat.beq c (nat_lit 2)) (Prod.mk (nat_lit 1) (mEbs d.FT (Nat.land p (nat_lit 1)) (f16 p (nat_lit 1)) s))
      (bsel (Nat.beq c (nat_lit 3)) (Prod.mk (nat_lit 1) (mTfs d.FT d.OT k.TH (Nat.land p (nat_lit 1))
          (f16 p (nat_lit 1)) (Nat.land (Nat.shiftRight p (nat_lit 17)) (nat_lit 7))
          (Nat.land (Nat.shiftRight p (nat_lit 20)) mask144) s))
      (bsel (Nat.beq c (nat_lit 4)) (Prod.mk (nat_lit 1) (mTbs d.FT d.OT k.TH (Nat.land p (nat_lit 1))
          (f16 p (nat_lit 1)) (Nat.land (Nat.shiftRight p (nat_lit 17)) (nat_lit 7))
          (Nat.land (Nat.shiftRight p (nat_lit 20)) mask144) (Nat.land (Nat.shiftRight p (nat_lit 164)) mask144) s))
      (bsel (andB tr (Nat.beq c (nat_lit 10))) (Prod.mk (Nat.mul (nat_lit 2) (trEnd s)) bad4)
      (bsel (andB (Bool.rec (motive := fun _ => Bool) true false tr) (Nat.beq c (nat_lit 6)))
        (Prod.mk (Nat.mul (nat_lit 2) (mEndJ s)) bad4)
        mFail)))))))) q

@[expose] noncomputable def forceK {α : Type} (q : Nat × St) (f : Nat × St → α) : α :=
  Prod.rec (motive := fun _ => α) (fun m s => strictT m (fun m' =>
    Prod.rec (motive := fun _ => α) (fun d pc => strictT d (fun d' =>
      Prod.rec (motive := fun _ => α) (fun p c => strictT p (fun p' => strictT c (fun c' =>
        f (Prod.mk m' (Prod.mk d' (Prod.mk p' c')))))) pc)) s)) q

@[expose] noncomputable def forceM {α : Type} (q : Nat × St4) (f : Nat × St4 → α) : α :=
  Prod.rec (motive := fun _ => α) (fun m s => strictT m (fun m' =>
    Prod.rec (motive := fun _ => α) (fun d r => strictT d (fun d' =>
      Prod.rec (motive := fun _ => α) (fun p r2 => strictT p (fun p' =>
        Prod.rec (motive := fun _ => α) (fun n c => strictT n (fun n' => strictT c (fun c' =>
          f (Prod.mk m' (Prod.mk d' (Prod.mk p' (Prod.mk n' c'))))))) r2)) r)) s)) q

@[expose] noncomputable def endK (q : Nat × St) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun m _ =>
    bsel (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 0)) (Nat.shiftRight m (nat_lit 1)) FAIL) q
@[expose] noncomputable def endM (q : Nat × St4) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun m _ =>
    bsel (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 0)) (Nat.shiftRight m (nat_lit 1)) FAIL) q

@[expose] noncomputable def chunkK (k : KD) (C x : Nat) : Nat :=
  endK (Nat.rec (motive := fun _ => Nat → Nat × St → Nat × St) (fun _ q => q)
    (fun _ ih r q => strictT r (fun r => strictT (Nat.land r (nat_lit 15)) (fun c =>
      strictT (Nat.land (Nat.shiftRight r (nat_lit 4)) mPay) (fun p =>
        forceK (kStep k c p q) (ih (Nat.shiftRight r (Nat.add (nat_lit 4) (wK c))))))))
    (Nat.land C (nat_lit 16777215)) (Nat.shiftRight C (nat_lit 24))
    (Prod.mk (Nat.mul (nat_lit 2) x) bad))

@[expose] noncomputable def chunkM (d : MD) (k : KD) (tr : Bool) (C x : Nat) : Nat :=
  endM (Nat.rec (motive := fun _ => Nat → Nat × St4 → Nat × St4) (fun _ q => q)
    (fun _ ih r q => strictT r (fun r => strictT (Nat.land r (nat_lit 15)) (fun c =>
      strictT (Nat.land (Nat.shiftRight r (nat_lit 4)) mPay) (fun p =>
        forceM (mStep d k tr c p q) (ih (Nat.shiftRight r (Nat.add (nat_lit 4) (wM c))))))))
    (Nat.land C (nat_lit 16777215)) (Nat.shiftRight C (nat_lit 24))
    (Prod.mk (Nat.mul (nat_lit 2) x) bad4))

@[expose] noncomputable def runK (k : KD) (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (chunkK k C S) ih) l x

@[expose] noncomputable def runM (d : MD) (k : KD) (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (chunkM d k false C S) ih) l x

@[expose] noncomputable def runT (d : MD) (k : KD) (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (chunkM d k true C S) ih) l x

@[expose] noncomputable def runF (k : KD) (D : Nat) (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S =>
    strictN (forRun k.FT k.PT k.OT k.ND k.NOM D (Nat.shiftRight C (nat_lit 12)) (Nat.land C (nat_lit 4095)) S) ih) l x

@[expose] noncomputable def allIn (a b : Nat) (f : Nat → Bool) : Bool :=
  rngAll a b (Nat.add (Nat.shiftRight (Nat.sub b a) (nat_lit 6)) (nat_lit 1)) f

@[expose] noncomputable def kSetup (k : KD) : Bool :=
  andB (chkEq k.INV invKR) (andB (ptOK k.TH) (andB (chkEq (k.PT k.i0) k.TH)
  (andB (chkEq (letMat k.LET (nat_lit 4)) (nat_lit 0))
  (andB (chkInv (letMat k.LET (nat_lit 0)) (letMat k.LET (nat_lit 1)))
  (andB (chkInv (letMat k.LET (nat_lit 2)) (letMat k.LET (nat_lit 3)))
  (andB (chkInv (letMat k.LET (nat_lit 5)) (letMat k.LET (nat_lit 6)))
  (andB (Nat.blt k.LET (Nat.shiftLeft (nat_lit 1) (nat_lit 1008)))
  (andB (allIn (nat_lit 0) (nat_lit 12) (relAt k.RT k.LET))
  (andB (allIn (nat_lit 0) (nat_lit 88) (rzAt k.RZT k.LET))
  (andB (chkEval k.LET (wW k.PAW) (wN k.PAW) k.TR1) (andB (chkEval k.LET (wW k.PBW) (wN k.PBW) k.PS1)
  (andB (chkTrans k.TR1) (andB (chkPt k.TH k.TR1 k.TH (nat_lit 0))
  (andB (chkEq (k.RZT (nat_lit 88)) (psiWord k.INV k.PAW k.PBW))
  (andB (wFits (wW k.W0W) (wN k.W0W)) (chkEval k.LET (wW k.W0W) (wN k.W0W) k.W0))))))))))))))))

@[expose] noncomputable def kHdr (k : KD) : Bool := allIn (nat_lit 0) k.nH (hOK k.HT k.LET (nat_lit 7) k.TR1 k.PS1)

@[expose] noncomputable def kPts (k : KD) : Bool :=
  andB (allIn (nat_lit 0) k.NOM (ptAt k.PT)) (allIn (nat_lit 0) k.NOM (omAt k.HT k.PT k.OT k.TH))

@[expose] noncomputable def kLam (k : KD) : Bool :=
  andB (allIn (nat_lit 0) (nat_lit 9) (conjOK k.CT k.LET k.TH k.TR1 k.PS1))
  (andB (allIn (nat_lit 0) (nat_lit 512) (lamOK k.LT k.CT k.TH))
  (andB (Nat.blt (lamCols k.LT (nat_lit 512)) (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)))
  (andB (allIn (nat_lit 0) (nat_lit 12) (wordAt k.RT k.WT k.INV))
  (andB (andB (psiGenOK k.RT k.HT k.LET k.INV k.TH (nat_lit 8) (nat_lit 1) (nat_lit 1) (nat_lit 1) (nat_lit 1)
      k.hx (nat_lit 2)) (chkEq (hMat (k.HT k.hx)) (letMat k.LET (nat_lit 0))))
    (andB (psiGenOK k.RT k.HT k.LET k.INV k.TH (nat_lit 9) k.sw k.sn k.sw k.sn k.hw (nat_lit 1))
      (chkInv (hMat (k.HT k.hw)) k.W0))))))

@[expose] noncomputable def fullOf (k : KD) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) k.NOM) (nat_lit 1)

@[expose] noncomputable def forAll (k : KD) (Ls : List (List Nat)) (D₁ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun L _ ih D =>
    andB (Nat.beq (runF k D L (nat_lit 0)) (fullOf k)) (ih (Nat.succ D))) Ls D₁

@[expose] noncomputable def chAll (k : KD) (Ls : List ((Nat → Nat) × (Nat × (List Nat × Nat)))) (D₁ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun c _ ih D =>
    andB (Prod.rec (motive := fun _ => Bool) (fun E r => Prod.rec (motive := fun _ => Bool) (fun ne r2 =>
      Prod.rec (motive := fun _ => Bool) (fun lv bd =>
        andB (Nat.beq (chainRun k.FT E k.LET k.W0 k.TR1 D (nat_lit 256) ne lv) bd)
          (andB (Nat.blt (nat_lit 0) bd) (Nat.beq (Nat.mod k.BK bd) (nat_lit 0)))) r2) r) c)
      (ih (Nat.succ D))) Ls D₁

@[expose] noncomputable def idxSum (k : KD) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1) (fun c _ ih =>
    Nat.add ih (Nat.div k.BK c.2.2.2)) k.DCH

@[expose] noncomputable def kChains (k : KD) : Bool :=
  andB (Nat.beq (chainRun k.FT k.EK k.LET k.W0 k.TR1 (nat_lit 65535) (nat_lit 37) k.neK k.LVK) k.BK)
  (andB (Nat.beq (chainRun k.FT k.EN k.LET k.W0 k.TR1 (nat_lit 65535) (nat_lit 5) k.neN k.LVN) k.BN)
  (andB (Nat.beq (chainRun k.FT k.ET0 k.LET k.W0 k.TR1 (nat_lit 65535) (nat_lit 513) k.neT0 k.LVT0) k.BT0)
  (andB (Nat.beq (chainRun k.FT k.ET k.LET k.W0 k.TR1 (nat_lit 65535) (nat_lit 1537) k.neT k.LVT) k.BT)
  (andB (Nat.beq (List.length k.DCH) (Nat.sub k.ND (nat_lit 1))) (andB (chAll k k.DCH (nat_lit 1))
  (andB (chkEq k.BK (Nat.mul (nat_lit 2048) k.BN)) (andB (chkEq k.BK (Nat.mul k.NOM k.BT))
    (chkEq k.BK (Nat.mul (Nat.mul k.NOM (nat_lit 512)) k.BT0)))))))))

@[expose] noncomputable def kRange (k : KD) : Bool :=
  andB (Nat.blt (nat_lit 0) k.ND) (andB (Nat.blt k.ND (nat_lit 65535)) (andB (Nat.blt k.NF (nat_lit 1048576))
  (andB (Nat.blt (nat_lit 0) k.NOM) (andB (Nat.blt k.NOM (nat_lit 32768))
  (andB (allIn (nat_lit 0) (nat_lit 12) (fun r => letsBelow (wW (k.RT r)) (wN (k.RT r)) (nat_lit 5)))
  (andB (cov0 k.FT k.ND k.cv)
  (andB (Nat.beq k.INV (nat_lit 0x5060402030001)) (andB (KShape.wordsOK k.WREC)
  (andB (KShape.sqOK k.RZT k.INV k.WREC) (andB (KShape.commOK k.RZT k.INV k.WREC (nat_lit 0) (nat_lit 11))
    (KShape.conjOK k.RZT k.INV k.WREC k.CM)))))))))))

@[expose] noncomputable def mSetup (d : MD) (k : KD) : Bool :=
  andB (allIn (nat_lit 0) d.nH (hOK d.HT k.LET (nat_lit 4) (nat_lit 0) (nat_lit 0)))
  (andB (allIn (nat_lit 0) d.NOM (omAtm d.HT d.OT k.TH)) (andB (allIn (nat_lit 0) d.nSG (segAt d.SG k.LET))
  (andB (allIn (nat_lit 0) d.nW (wordAt k.RT d.WT k.INV))
  (andB (chkEq d.ZW (zWord k.INV)) (andB (allIn (nat_lit 0) (nat_lit 89) (linkAt k.RZT d.TW k.INV d.ZW))
  (andB (Nat.blt (nat_lit 0) d.ND) (andB (Nat.blt d.ND (nat_lit 65535)) (Nat.blt d.NF (nat_lit 1048576)))))))))

@[expose] noncomputable def j4Ok (k : KD) (d : MD) (KW MW MT : List Nat) (FLs : List (List Nat)) : Bool :=
  andB (kSetup k) (andB (kHdr k) (andB (kPts k) (andB (kLam k)
  (andB (Nat.beq (runK k KW (mkC (nat_lit 0) (nat_lit 1))) (mkC k.NF k.ND))
  (andB (Nat.beq (List.length FLs) (Nat.sub k.ND (nat_lit 1))) (andB (forAll k FLs (nat_lit 1))
  (andB (kChains k) (andB (kRange k) (andB (mSetup d k)
  (andB (Nat.beq (runM d k MW (mkC (nat_lit 0) (nat_lit 1))) (mkC d.NF d.ND))
    (Nat.beq (runT d k MT (nat_lit 0)) (nat_lit 89))))))))))))

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem runK_append (k : KD) : ∀ (l1 l2 : List Nat) (x : Nat),
    runK k (List.append l1 l2) x = runK k l2 (runK k l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (chunkK k C x) (runK k (List.append l1 l2)) = runK k l2 (strictN (chunkK k C x) (runK k l1))
    rw [strictN_eq, strictN_eq]
    exact runK_append k l1 l2 _

theorem runM_append (d : MD) (k : KD) : ∀ (l1 l2 : List Nat) (x : Nat),
    runM d k (List.append l1 l2) x = runM d k l2 (runM d k l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (chunkM d k false C x) (runM d k (List.append l1 l2)) =
      runM d k l2 (strictN (chunkM d k false C x) (runM d k l1))
    rw [strictN_eq, strictN_eq]
    exact runM_append d k l1 l2 _

theorem runT_append (d : MD) (k : KD) : ∀ (l1 l2 : List Nat) (x : Nat),
    runT d k (List.append l1 l2) x = runT d k l2 (runT d k l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (chunkM d k true C x) (runT d k (List.append l1 l2)) =
      runT d k l2 (strictN (chunkM d k true C x) (runT d k l1))
    rw [strictN_eq, strictN_eq]
    exact runT_append d k l1 l2 _

theorem runF_append (k : KD) (D : Nat) : ∀ (l1 l2 : List Nat) (x : Nat),
    runF k D (List.append l1 l2) x = runF k D l2 (runF k D l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (forRun k.FT k.PT k.OT k.ND k.NOM D (Nat.shiftRight C (nat_lit 12)) (Nat.land C (nat_lit 4095)) x)
        (runF k D (List.append l1 l2)) =
      runF k D l2 (strictN (forRun k.FT k.PT k.OT k.ND k.NOM D (Nat.shiftRight C (nat_lit 12))
        (Nat.land C (nat_lit 4095)) x) (runF k D l1))
    rw [strictN_eq, strictN_eq]
    exact runF_append k D l1 l2 _

theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

theorem forAll_cons (k : KD) (L : List Nat) (Ls : List (List Nat)) (D : Nat) :
    forAll k (L :: Ls) D = andB (Nat.beq (runF k D L (nat_lit 0)) (fullOf k)) (forAll k Ls (Nat.succ D)) :=
  rfl

theorem forAll_nil (k : KD) (D : Nat) : forAll k [] D = true := rfl

end CFSG.KJ4.R

end
