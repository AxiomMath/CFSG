module

public import Certificates.Data.Kernel.LyOmega.Tree

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord

structure SConsts where
  Lb : Nat
  Hb : Nat
  CMb : Nat
  L7 : Nat
  H7 : Nat
  CM7 : Nat
  ONE : Nat

@[expose] noncomputable def sConstsOK (C : SConsts) : Bool :=
  bAnd(Nat.beq C.Lb (rep1 (nat_lit 11) (nat_lit 3136)),
  bAnd(Nat.beq C.Hb (Nat.shiftLeft C.Lb (nat_lit 10)),
  bAnd(Nat.beq C.CMb (Nat.mul (nat_lit 2047) (rep1 (nat_lit 539) (nat_lit 64))),
  bAnd(Nat.beq C.L7 (rep1 (nat_lit 11) (nat_lit 49)),
  bAnd(Nat.beq C.H7 (Nat.shiftLeft C.L7 (nat_lit 10)),
  bAnd(Nat.beq C.CM7 (Nat.mul (nat_lit 2047) (rep1 (nat_lit 77) (nat_lit 7))),
    Nat.beq C.ONE (rep1 (nat_lit 88) (nat_lit 7))))))))

@[expose] noncomputable def sMul (C : SConsts) (X Y : Nat) : Nat :=
  mulR (nat_lit 5) (nat_lit 11) (nat_lit 77) (nat_lit 7) (nat_lit 7) C.L7 C.H7 C.CM7
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 77)) (nat_lit 1)) X Y

@[expose] noncomputable def sBlk (C : SConsts) (X K : Nat) : Nat :=
  rowsMulR (nat_lit 5) (nat_lit 11) (nat_lit 539) (nat_lit 7) (nat_lit 7) (nat_lit 7) C.Lb C.Hb
    C.CMb (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 539)) (nat_lit 1)) X K

@[expose] noncomputable def sVld (C : SConsts) (X : Nat) : Bool :=
  validM (nat_lit 5) (nat_lit 539) C.L7 C.H7 X

@[expose] noncomputable def sEnt (X i j : Nat) : Nat :=
  fldW X (Nat.add (Nat.mul (nat_lit 77) i) (Nat.mul (nat_lit 11) j)) (nat_lit 11)

@[expose] noncomputable def kronOK (A B K : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight K (nat_lit 26411)) (nat_lit 0),
    allBelow (nat_lit 2401) (nat_lit 38) (fun t =>
      (fun r c => Nat.beq (fldW K (Nat.add (Nat.mul (nat_lit 539) r) (Nat.mul (nat_lit 11) c)) (nat_lit 11))
        (Nat.mod (Nat.mul (sEnt A (Nat.div r (nat_lit 7)) (Nat.div c (nat_lit 7)))
          (sEnt B (Nat.mod r (nat_lit 7)) (Nat.mod c (nat_lit 7)))) (nat_lit 5)))
      (Nat.div t (nat_lit 49)) (Nat.mod t (nat_lit 49))))

@[expose] noncomputable def sTr (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => (fun i j => Nat.lor acc (Nat.shiftLeft (sEnt X i j)
        (Nat.add (Nat.mul (nat_lit 77) j) (Nat.mul (nat_lit 11) i))))
      (Nat.div t (nat_lit 7)) (Nat.mod t (nat_lit 7))) (nat_lit 49)

@[expose] noncomputable def sRec (PT : Nat → Nat) (i : Nat) : Nat := getRec PT (nat_lit 22) i

@[expose] noncomputable def sGather (KX PT : Nat → Nat) (n b s : Nat) (self : Bool) : Nat :=
  strictN (PT b) (fun P => strictN (KX b) (fun K =>
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
      (fun k ih acc cnt =>
        (fun r => strictN (fldW P (Nat.mul (nat_lit 22) r) (nat_lit 22)) (fun e =>
          nIf(bAnd(isChild n (Nat.add (Nat.shiftLeft b (nat_lit 6)) r),
              Nat.beq (Nat.shiftRight e (nat_lit 20)) s),
            ih (Nat.lor acc (Nat.shiftLeft
              (Bool.rec (motive := fun _ => Nat)
                (getRec KX (nat_lit 539) (Nat.land e (nat_lit 1048575)))
                (fldW K (Nat.mul (nat_lit 539) r) (nat_lit 539)) self)
              (Nat.mul (nat_lit 539) cnt))) (Nat.succ cnt),
            ih acc cnt)))
        (Nat.sub (nat_lit 63) k))
      (nat_lit 64) (nat_lit 0) (nat_lit 0)))

@[expose] noncomputable def sBad (PT : Nat → Nat) (m n b : Nat) : Nat :=
  strictN (PT b) (fun P => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => (fun i => (fun e => nIf(isChild n i,
        nIf(bAnd(Nat.blt (Nat.land e (nat_lit 1048575)) i, Nat.blt (Nat.shiftRight e (nat_lit 20)) m),
          acc, Nat.succ acc), acc))
        (fldW P (Nat.mul (nat_lit 22) r) (nat_lit 22)))
      (Nat.add (Nat.shiftLeft b (nat_lit 6)) r)) (nat_lit 64))

@[expose] noncomputable def sLeaf (C : SConsts) (KX PT : Nat → Nat) (Ks : List Nat) (m n b : Nat) :
    Bool :=
  bAnd(Nat.beq (sBad PT m n b) (nat_lit 0),
    Nat.rec (motive := fun _ => Bool) true
      (fun s ih => bAnd(Nat.beq (sBlk C (sGather KX PT n b s false) (pickL Ks s))
        (sGather KX PT n b s true), ih)) m)

@[expose] noncomputable def sRange (C : SConsts) (KX PT : Nat → Nat) (Ks : List Nat) (m n b₀ c : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => bAnd(sLeaf C KX PT Ks m n (Nat.add b₀ j), ih)) c

@[expose] noncomputable def sSort (KX SG : Nat → Nat) (n k₀ c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1)) (fun j =>
    (fun k => letB (getRec SG (nat_lit 20) k) (fun a =>
        letB (getRec SG (nat_lit 20) (Nat.succ k)) (fun b =>
          bAnd(Nat.blt a n, bAnd(Nat.blt b n,
            Nat.blt (getRec KX (nat_lit 539) a) (getRec KX (nat_lit 539) b))))))
      (Nat.add k₀ j))

@[expose] noncomputable def sSub1 (C : SConsts) (X : Nat) : Nat :=
  redP (nat_lit 11) C.L7 C.H7 (nat_lit 5) (nat_lit 7) (Nat.add X (Nat.mul (nat_lit 4) C.ONE))

@[expose] noncomputable def sTrace (X : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (sEnt X i i)) (nat_lit 7)) (nat_lit 5)

@[expose] noncomputable def sRk1 (X : Nat) : Bool :=
  allBelow (nat_lit 2401) (nat_lit 38) (fun t =>
    (fun i k j l => bIf(bAnd(Nat.blt i k, Nat.blt j l),
        Nat.beq (Nat.mod (Nat.add (Nat.mul (sEnt X i j) (sEnt X k l))
          (Nat.mul (nat_lit 4) (Nat.mul (sEnt X i l) (sEnt X k j)))) (nat_lit 5)) (nat_lit 0), true))
      (Nat.div t (nat_lit 343)) (Nat.mod (Nat.div t (nat_lit 49)) (nat_lit 7))
      (Nat.mod (Nat.div t (nat_lit 7)) (nat_lit 7)) (Nat.mod t (nat_lit 7)))

@[expose] noncomputable def sClass (C : SConsts) (X : Nat) : Nat :=
  (fun ne1 =>
    Nat.add (nIf(bAnd(ne1, Nat.beq (sMul C X X) C.ONE), nat_lit 1, nat_lit 0))
    (Nat.add (nIf(bAnd(ne1, bAnd(Nat.beq (sMul C (sMul C X X) X) C.ONE,
        Nat.beq (sTrace X) (nat_lit 1))),
      Nat.shiftLeft (nat_lit 1) (nat_lit 16), nat_lit 0))
    (nIf(bAnd(ne1, Nat.beq (sMul C (sMul C (sMul C X X) X) (sMul C X X)) C.ONE),
      nIf(Nat.beq (sMul C (sSub1 C X) (sSub1 C X)) (nat_lit 0), Nat.shiftLeft (nat_lit 1) (nat_lit 32),
        nIf(sRk1 (sMul C (sSub1 C X) (sSub1 C X)), nat_lit 0, Nat.shiftLeft (nat_lit 1) (nat_lit 48))),
      nat_lit 0))))
  (bIf(Nat.beq X C.ONE, false, true))

@[expose] noncomputable def sCountLeaf (C : SConsts) (KX : Nat → Nat) (n b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => strictN acc (fun a =>
      nIf(Nat.blt (Nat.add (Nat.shiftLeft b (nat_lit 6)) r) n,
        Nat.add a (sClass C (fldW (KX b) (Nat.mul (nat_lit 539) r) (nat_lit 539))), a))) (nat_lit 64)

@[expose] noncomputable def sCountRange (C : SConsts) (KX CT : Nat → Nat) (n b₀ c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1)) (fun j =>
    Nat.beq (sCountLeaf C KX n (Nat.add b₀ j)) (getRec CT (nat_lit 64) (Nat.add b₀ j)))

@[expose] noncomputable def sCountSum (CT : Nat → Nat) (nl : Nat) : Nat :=
  sumBelow nl (Nat.add (Nat.shiftRight nl (nat_lit 6)) (nat_lit 1)) (fun b => getRec CT (nat_lit 64) b)

end CFSG.KC.LyOm

end
