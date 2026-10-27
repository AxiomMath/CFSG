module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KC.CLog

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KS.Row

@[expose] noncomputable def fdK (FD : Nat → Nat) (i : Nat) : Nat :=
  rg (nat_lit 34) (nat_lit 17179869183) FD (nat_lit 0) i

@[expose] noncomputable def fl (e s m : Nat) : Nat := Nat.land (Nat.shiftRight e s) m

@[expose] noncomputable def kindOf (e : Nat) : Nat := Nat.land e (nat_lit 3)

@[expose] noncomputable def aOf (e : Nat) : Nat := fl e (nat_lit 2) (nat_lit 16383)

@[expose] noncomputable def xOf (e : Nat) : Nat := fl e (nat_lit 16) (nat_lit 15)

@[expose] noncomputable def bOf (e : Nat) : Nat := fl e (nat_lit 20) (nat_lit 16383)

@[expose] noncomputable def failK : Nat := nat_lit 1073741824

@[expose] noncomputable def stK (q p : Nat) : Nat := Nat.add (Nat.shiftLeft q (nat_lit 8)) p

@[expose] noncomputable def letK (RL RN : Nat → Nat) (W x off p : Nat) : Nat :=
  strictN (Nat.land W (nat_lit 3)) (fun o => nIf(Nat.blt o (nat_lit 2),
    strictN (fl W (nat_lit 8) (nat_lit 255)) (fun r => strictN (RN r) (fun n =>
    strictN (Nat.mod (Nat.add (fl W (nat_lit 2) (nat_lit 63)) (Nat.add p off)) n) (fun i =>
      nIf(Nat.beq o (nat_lit 0), pg (nat_lit 4) (nat_lit 15) (RL r) i,
        Nat.xor (pg (nat_lit 4) (nat_lit 15) (RL r) (Nat.sub (Nat.pred n) i)) (nat_lit 1))))),
    nIf(Nat.beq o (nat_lit 2), nIf(Nat.beq p (nat_lit 0), Nat.xor x (nat_lit 1), x), x)))

@[expose] noncomputable def stepK (FD SD : Nat → Nat) (L : Nat → Nat) (t s S : Nat) : Nat :=
  nIf(Nat.beq S failK, failK, strictN (r32 SD s) (fun d => strictN (Nat.shiftRight d (nat_lit 1))
    (fun f => nIf(Nat.blt f t, strictN (fdK FD f) (fun e =>
      strictN (Nat.shiftRight S (nat_lit 8)) (fun q => strictN (Nat.land S (nat_lit 255)) (fun p =>
      nIf(Nat.beq (kindOf e) (nat_lit 3),
        nIf(Nat.beq (Nat.land d (nat_lit 1)) (nat_lit 0),
          nIf(Nat.beq q (aOf e), stK (bOf e) p, failK),
          nIf(Nat.beq q (bOf e), stK (aOf e) p, failK)),
        nIf(Nat.beq (Nat.land d (nat_lit 1)) (nat_lit 0),
          nIf(bAnd(Nat.blt p (nat_lit 255), bAnd(Nat.beq q (aOf e), Nat.beq (L p) (xOf e))),
            stK (bOf e) (Nat.succ p), failK),
          nIf(bAnd(Nat.blt p (nat_lit 255),
              bAnd(Nat.beq q (bOf e), Nat.beq (L p) (Nat.xor (xOf e) (nat_lit 1)))),
            stK (aOf e) (Nat.succ p), failK)))))), failK))))

@[expose] noncomputable def walkK (FD SD : Nat → Nat) (L : Nat → Nat) (t b len S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun j ih S => strictN (stepK FD SD L t (Nat.sub (Nat.add b len) (Nat.succ j)) S) ih) len S

@[expose] noncomputable def walkOK (FD FS SD : Nat → Nat) (L : Nat → Nat) (t u v n : Nat) : Bool :=
  strictB (r32 FS t) (fun b => strictB (r32 FS (Nat.succ t)) (fun b' => bAnd(Nat.ble b b',
    Nat.beq (walkK FD SD L t b (Nat.sub b' b) (stK u (nat_lit 0))) (stK v n))))

@[expose] noncomputable def rangeK (m nR NC e W : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) (aOf e), bAnd(Nat.blt (aOf e) NC,
  bAnd(Nat.blt (nat_lit 0) (bOf e), bAnd(Nat.blt (bOf e) NC,
  bAnd(Nat.blt (xOf e) (Nat.mul (nat_lit 2) m),
    bIf(Nat.blt (Nat.land W (nat_lit 3)) (nat_lit 2), Nat.blt (fl W (nat_lit 8) (nat_lit 255)) nR,
      true))))))

@[expose] noncomputable def ruleK (SM : Nat) (RL RN FD FS SD DT : Nat → Nat) (t e W : Nat) : Bool :=
  strictB (kindOf e) (fun k => strictB (aOf e) (fun a => strictB (bOf e) (fun b =>
  strictB (xOf e) (fun x => strictB (Nat.land W (nat_lit 3)) (fun o =>
  bIf(Nat.beq k (nat_lit 0),
    bAnd(Nat.ble (nat_lit 2) b, bAnd(Nat.beq (r32 DT b) t,
      bAnd(bIf(Nat.beq a (nat_lit 1), true, Nat.blt (r32 DT a) t),
        Nat.beq (r32 FS t) (r32 FS (Nat.succ t))))),
  bIf(Nat.beq k (nat_lit 1),
    bAnd(Nat.beq a (nat_lit 1), bAnd(Nat.beq b (nat_lit 1),
      bAnd(Nat.beq (fl SM x (nat_lit 1)) (nat_lit 1), Nat.beq (r32 FS t) (r32 FS (Nat.succ t))))),
  bIf(Nat.beq k (nat_lit 2),
    bIf(Nat.blt o (nat_lit 2),
      bAnd(Nat.beq (letK RL RN W x (nat_lit 0) (nat_lit 0)) x,
        walkOK FD FS SD (letK RL RN W x (nat_lit 1)) t b a
          (Nat.pred (RN (fl W (nat_lit 8) (nat_lit 255))))),
      bAnd(Nat.beq o (nat_lit 3), walkOK FD FS SD (letK RL RN W x (nat_lit 0)) t a b (nat_lit 1))),
    walkOK FD FS SD (letK RL RN W x (nat_lit 0)) t a b
      (nIf(Nat.blt o (nat_lit 2), RN (fl W (nat_lit 8) (nat_lit 255)),
        nIf(Nat.beq o (nat_lit 2), nat_lit 2, nat_lit 0)))))))))))

@[expose] noncomputable def factK (m nR NC SM : Nat) (RL RN FD FS FW SD DT : Nat → Nat) (t : Nat) :
    Bool :=
  strictB (fdK FD t) (fun e => strictB (r32 FW t) (fun W =>
    bAnd(rangeK m nR NC e W, ruleK SM RL RN FD FS SD DT t e W)))

@[expose] noncomputable def factSlK (m nR NC SM NF : Nat) (RL RN FD FS FW SD DT : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun t =>
    bIf(Nat.blt t NF, factK m nR NC SM RL RN FD FS FW SD DT t, true)))

@[expose] noncomputable def defK (NF : Nat) (FD DT : Nat → Nat) (b : Nat) : Bool :=
  bIf(Nat.blt b (nat_lit 2), true, strictB (r32 DT b) (fun t => bAnd(Nat.blt t NF,
    strictB (fdK FD t) (fun e => bAnd(Nat.beq (kindOf e) (nat_lit 0), Nat.beq (bOf e) b)))))

@[expose] noncomputable def wordK (m : Nat) (w : List Nat) (P n : Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
    (fun c _ ih j => bAnd(Nat.blt c (Nat.mul (nat_lit 2) m),
      bAnd(Nat.beq (pg (nat_lit 4) (nat_lit 15) P j) c, strictB (Nat.succ j) ih))) w) (nat_lit 0)

@[expose] noncomputable def relsK (m nR : Nat) (rels : List (List Nat)) (RL RN : Nat → Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i nR)
    (fun w _ ih i => bAnd(Nat.blt (nat_lit 0) (RN i), bAnd(Nat.blt (RN i) (nat_lit 255),
      bAnd(wordK m w (RL i) (RN i), strictB (Nat.succ i) ih)))) rels) (nat_lit 0)

@[expose] noncomputable def subsK (m : Nat) (subs : List Nat) (SM : Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true
      (fun c _ ih => bAnd(Nat.blt c (Nat.mul (nat_lit 2) m), ih)) subs,
    Nat.beq SM (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) c) ih) subs))

@[expose] noncomputable def hdK (m nR NF FIN SM z : Nat) (rels : List (List Nat)) (subs : List Nat)
    (RL RN FD : Nat → Nat) : Bool :=
  bAnd(Nat.ble m (nat_lit 8), bAnd(relsK m nR rels RL RN, bAnd(subsK m subs SM,
  bAnd(Nat.blt z (Nat.mul (nat_lit 2) m), bAnd(Nat.blt FIN NF,
    strictB (fdK FD FIN) (fun e => bAnd(Nat.blt (kindOf e) (nat_lit 3),
      bAnd(Nat.beq (aOf e) (nat_lit 1), bAnd(Nat.beq (bOf e) (nat_lit 1), Nat.beq (xOf e) z)))))))))

end CFSG.KC.CLog

end
