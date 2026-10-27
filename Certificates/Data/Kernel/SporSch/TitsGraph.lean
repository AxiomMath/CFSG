module

public import Certificates.Data.Kernel.SporSch.TitsPrim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def pairFst (kk : Nat) : Nat := Nat.div kk 2

@[expose] noncomputable def pairSnd (kk : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod kk 2) 0, nIf(Nat.beq (Nat.div kk 2) 0, 1, 0),
    nIf(Nat.beq (Nat.div kk 2) 2, 1, 2))

@[expose] noncomputable def nbrRowK (n m d wB wL NB NL u i : Nat) : Bool :=
  strictB (pgW wB NB (Nat.add (Nat.mul d u) i)) (fun b =>
    bAnd(Nat.blt b n, bAnd(Nat.blt (pgW wL NL (Nat.add (Nat.mul d u) i)) m,
      bIf(Nat.blt (Nat.succ i) d,
        Nat.blt b (pgW wB NB (Nat.succ (Nat.add (Nat.mul d u) i))), true))))

@[expose] noncomputable def nbrPairK (d wB wL : Nat) (LP : Nat → Nat) (NB NL PW v kk : Nat) :
    Bool :=
  strictB (LP (Nat.add (Nat.mul 3 v) (pairFst kk))) (fun a =>
    strictB (LP (Nat.add (Nat.mul 3 v) (pairSnd kk))) (fun b =>
    strictB (pgW 4 PW (Nat.add (Nat.mul 6 v) kk)) (fun p => bAnd(Nat.blt p d,
    bAnd(Nat.beq (pgW wB NB (Nat.add (Nat.mul d a) p)) b,
      Nat.beq (pgW wL NL (Nat.add (Nat.mul d a) p)) v)))))

@[expose] noncomputable def nbrLineK (n d wB wL : Nat) (LP : Nat → Nat) (NB NL PW v : Nat) :
    Bool :=
  strictB (LP (Nat.mul 3 v)) (fun a0 => strictB (LP (Nat.succ (Nat.mul 3 v))) (fun a1 =>
    strictB (LP (Nat.add (Nat.mul 3 v) 2)) (fun a2 =>
    bAnd(Nat.blt a0 n, bAnd(Nat.blt a1 n, bAnd(Nat.blt a2 n,
    bAnd(bIf(Nat.beq a0 a1, false, true), bAnd(bIf(Nat.beq a0 a2, false, true),
    bAnd(bIf(Nat.beq a1 a2, false, true), allN 6 (nbrPairK d wB wL LP NB NL PW v))))))))))

@[expose] noncomputable def nbrK (n m d wB wL : Nat) (LP : Nat → Nat) (NB NL PW : Nat) : Bool :=
  bAnd(Nat.blt d 16, bAnd(Nat.beq (Nat.mul n d) (Nat.mul 6 m),
  bAnd(allN n (fun u => allN d (nbrRowK n m d wB wL NB NL u)),
    allN m (nbrLineK n d wB wL LP NB NL PW))))

@[expose] noncomputable def codeK (B d w SC C x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pgW w C x)
    (fun j acc => Nat.add (Nat.mul acc B) (pgW w SC (Nat.add (Nat.mul d x) j))) d

@[expose] noncomputable def permBits (d PI x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (pgW 4 PI (Nat.add (Nat.mul d x) j)))) d

@[expose] noncomputable def refNbK (n d w NB C SC PI x j : Nat) : Bool :=
  strictB (pgW 4 PI (Nat.add (Nat.mul d x) j)) (fun p => bAnd(Nat.blt p d,
    strictB (pgW w NB (Nat.add (Nat.mul d x) p)) (fun y => bAnd(Nat.blt y n,
    bAnd(Nat.beq (pgW w SC (Nat.add (Nat.mul d x) j)) (pgW w C y),
    bIf(Nat.blt (Nat.succ j) d, Nat.ble (pgW w SC (Nat.add (Nat.mul d x) j))
      (pgW w SC (Nat.succ (Nat.add (Nat.mul d x) j))), true))))))

@[expose] noncomputable def refPtK (n d B w NB C C' SC PI REP k x : Nat) : Bool :=
  strictB (pgW w C' x) (fun c => bAnd(Nat.blt c k,
    bAnd(Nat.beq (codeK B d w SC C x) (codeK B d w SC C (pgW w REP c)),
    bAnd(Nat.beq (permBits d PI x) (mask d), allN d (refNbK n d w NB C SC PI x)))))

@[expose] noncomputable def refRepK (n d B w C C' SC REP k c : Nat) : Bool :=
  strictB (pgW w REP c) (fun r => bAnd(Nat.blt r n,
    bAnd(Nat.beq (pgW w C' r) c, bIf(Nat.blt (Nat.succ c) k,
      Nat.blt (codeK B d w SC C r) (codeK B d w SC C (pgW w REP (Nat.succ c))), true))))

@[expose] noncomputable def refK (n d B w NB C C' SC PI REP k : Nat) : Bool :=
  bAnd(Nat.blt n 4294967296, bAnd(Nat.blt d 16, bAnd(Nat.ble k n,
  bAnd(allN n (refPtK n d B w NB C C' SC PI REP k), allN k (refRepK n d B w C C' SC REP k)))))

@[expose] noncomputable def numK (n w C k REP : Nat) : Bool :=
  bAnd(allN n (fun x => Nat.blt (pgW w C x) k),
    allN k (fun c => strictB (pgW w REP c) (fun r => bAnd(Nat.blt r n, Nat.beq (pgW w C r) c))))

end CFSG.KS.SporSch

end
