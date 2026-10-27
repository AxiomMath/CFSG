module

public import Certificates.Data.Kernel.LyOmega.Tree

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord

structure BConsts where
  L7 : Nat
  H7 : Nat
  CM7 : Nat
  ONE7 : Nat
  MASK7 : Nat
  LV : Nat
  HV : Nat
  LW : Nat
  HW : Nat
  LF : Nat
  HF : Nat
  CMF : Nat
  ONEF : Nat

@[expose] noncomputable def bConstsOK (C : BConsts) : Bool :=
  bAnd(Nat.beq C.L7 (rep1 (nat_lit 12) (nat_lit 777)),
  bAnd(Nat.beq C.H7 (Nat.shiftLeft C.L7 (nat_lit 11)),
  bAnd(Nat.beq C.CM7 (Nat.mul (nat_lit 4095) (rep1 (nat_lit 1332) (nat_lit 7))),
  bAnd(Nat.beq C.ONE7 (rep1 (nat_lit 1344) (nat_lit 7)),
  bAnd(Nat.beq C.MASK7 (Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 84)) (nat_lit 1))
      (rep1 (nat_lit 1332) (nat_lit 7))),
  bAnd(Nat.beq C.LV (rep1 (nat_lit 12) (nat_lit 111)),
  bAnd(Nat.beq C.HV (Nat.shiftLeft C.LV (nat_lit 11)),
  bAnd(Nat.beq C.LW (rep1 (nat_lit 12) (nat_lit 7)),
  bAnd(Nat.beq C.HW (Nat.shiftLeft C.LW (nat_lit 11)),
  bAnd(Nat.beq C.LF (rep1 (nat_lit 12) (nat_lit 12321)),
  bAnd(Nat.beq C.HF (Nat.shiftLeft C.LF (nat_lit 11)),
  bAnd(Nat.beq C.CMF (Nat.mul (nat_lit 4095) (rep1 (nat_lit 1332) (nat_lit 111))),
    Nat.beq C.ONEF (rep1 (nat_lit 1344) (nat_lit 111))))))))))))))

@[expose] noncomputable def rmB : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1332)) (nat_lit 1)

@[expose] noncomputable def bMul (C : BConsts) (X G : Nat) : Nat :=
  rowsMulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 37) (nat_lit 3) (nat_lit 8) C.L7 C.H7
    C.CM7 rmB X G

@[expose] noncomputable def bMul7 (C : BConsts) (M N : Nat) : Nat :=
  mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 7) (nat_lit 8) C.L7 C.H7 C.CM7 rmB M N

@[expose] noncomputable def bVec7 (C : BConsts) (x N : Nat) : Nat :=
  vecR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 7) (nat_lit 8) C.LV C.HV rmB x N

@[expose] noncomputable def bVec (C : BConsts) (y G : Nat) : Nat :=
  vecR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111) (nat_lit 8) C.LV C.HV rmB y G

@[expose] noncomputable def sameSpan (C : BConsts) (N Y : Nat) : Bool :=
  Nat.beq (bMul7 C (Nat.land Y C.MASK7) N) Y

@[expose] noncomputable def last7 (C : BConsts) (Y : Nat) : Nat :=
  Nat.land (Nat.shiftRight Y (nat_lit 1248)) C.MASK7

@[expose] noncomputable def sameSpanL (C : BConsts) (N Y : Nat) : Bool :=
  Nat.beq (bMul7 C (last7 C Y) N) Y

@[expose] noncomputable def witOK (C : BConsts) (WC : Nat → Nat) (N c w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun e ih => bAnd(letB (fldW w (Nat.mul (nat_lit 84) e) (nat_lit 84)) (fun x =>
        bAnd(bIf(Nat.beq x (nat_lit 0), false, true),
        bAnd(validM (nat_lit 5) (nat_lit 84) C.LW C.HW x,
          Nat.beq (fldW (bVec C (bVec7 C x N) (WC (Nat.add c (Nat.mul (nat_lit 8) e)))) (nat_lit 1248)
            (nat_lit 84)) (nat_lit 0)))), ih)) c

@[expose] noncomputable def chartOf (e : Nat) : Nat := fldW e (nat_lit 24) (nat_lit 4)

@[expose] noncomputable def cNode (C : BConsts) (KX PT WT GT WC : Nat → Nat) (nc n i : Nat) : Bool :=
  letB (getRec PT (nat_lit 32) i) (fun e =>
  letB (chartOf e) (fun c =>
  letB (getRec KX (nat_lit 9324) i) (fun N =>
  bAnd(Nat.blt c nc,
  bAnd(validM (nat_lit 5) (nat_lit 9324) C.L7 C.H7 N,
  bAnd(Nat.beq (last7 C N) C.ONE7,
  bAnd(witOK C WC N c (getRec WT (nat_lit 588) i),
    bIf(Nat.beq i (nat_lit 0), true,
      letB (fldW e (nat_lit 0) (nat_lit 20)) (fun p =>
      letB (fldW e (nat_lit 20) (nat_lit 4)) (fun s =>
      bAnd(Nat.blt p i, bAnd(Nat.blt s (nat_lit 2),
        letB (chartOf (getRec PT (nat_lit 32) p)) (fun cp =>
          sameSpanL C N (bMul C (getRec KX (nat_lit 9324) p)
            (GT (Nat.add s (Nat.add (Nat.mul (nat_lit 2) cp) (Nat.mul (nat_lit 16) c))))))))))))))))))

@[expose] noncomputable def cRange (C : BConsts) (KX PT WT GT WC : Nat → Nat) (nc n b₀ c : Nat) : Bool :=
  allBelow (Nat.mul (nat_lit 64) c) (c) (fun j =>
    (fun i => bIf(Nat.blt i n, cNode C KX PT WT GT WC nc n i, true))
      (Nat.add (Nat.shiftLeft b₀ (nat_lit 6)) j))

@[expose] noncomputable def cKey (KX PT : Nat → Nat) (i : Nat) : Nat :=
  Nat.add (getRec KX (nat_lit 9324) i)
    (Nat.shiftLeft (chartOf (getRec PT (nat_lit 32) i)) (nat_lit 9324))

@[expose] noncomputable def cSort (KX PT SG : Nat → Nat) (n k₀ c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1)) (fun j =>
    (fun k => letB (getRec SG (nat_lit 20) k) (fun a =>
        letB (getRec SG (nat_lit 20) (Nat.succ k)) (fun b =>
          bAnd(Nat.blt a n, bAnd(Nat.blt b n, Nat.blt (cKey KX PT a) (cKey KX PT b))))))
      (Nat.add k₀ j))

@[expose] noncomputable def cFix (C : BConsts) (KX PT XM : Nat → Nat) (n b₀ c : Nat) : Nat :=
  sumBelow (Nat.mul (nat_lit 64) c) c (fun j =>
    (fun i => nIf(bAnd(Nat.blt i n,
          sameSpanL C (getRec KX (nat_lit 9324) i)
            (bMul C (getRec KX (nat_lit 9324) i) (XM (chartOf (getRec PT (nat_lit 32) i))))),
        nat_lit 1, nat_lit 0))
      (Nat.add (Nat.shiftLeft b₀ (nat_lit 6)) j))

@[expose] noncomputable def bEnt (X i j : Nat) : Nat :=
  fldW X (Nat.add (Nat.mul (nat_lit 1332) i) (Nat.mul (nat_lit 12) j)) (nat_lit 12)

@[expose] noncomputable def trOK (r c X Y : Nat) : Bool :=
  allBelow (Nat.mul r c) (Nat.add (Nat.shiftRight (Nat.mul r c) (nat_lit 6)) (nat_lit 1)) (fun t =>
    (fun i j => Nat.beq (bEnt X i j) (bEnt Y j i)) (Nat.div t c) (Nat.mod t c))

@[expose] noncomputable def fMul (C : BConsts) (X Y : Nat) : Nat :=
  mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111) (nat_lit 8) C.LF C.HF C.CMF rmB X Y

@[expose] noncomputable def fVld (C : BConsts) (X : Nat) : Bool :=
  validM (nat_lit 5) (nat_lit 147852) C.LF C.HF X

end CFSG.KC.LyOm

end
