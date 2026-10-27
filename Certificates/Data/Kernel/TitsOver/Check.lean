module

public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.TitsOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.KS.Mathieu

@[expose] noncomputable def baseEqK (w m nb : Nat) (B : Nat → Nat) (p g t : Nat) : Bool :=
  allN nb (fun s => strictB (B s) (fun b => Nat.beq (pg w m p b) (pg w m g (pg w m t b))))

@[expose] noncomputable def penumPtBK (n w m nw : Nat) (G : Nat → Nat) (k cnt nb : Nat)
    (B T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq t (pcomp n w m (G l) (T p)),
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(baseEqK w m nb B (T q) (G j) t,
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def penumSlBK (n w m nw : Nat) (G : Nat → Nat) (k cnt nb : Nat)
    (B T PL POS SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, penumPtBK n w m nw G k cnt nb B T PL POS SRT SRI i, true)))

@[expose] noncomputable def letF (Lf Li : Nat → Nat → Nat) (c y : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    Lf (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) y,
    Li (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) y)

@[expose] noncomputable def wordPtK (F : Nat → Nat → Nat) (wd : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => F (icode z) y)) wd x

@[expose] noncomputable def wordBK (kL nb : Nat) (B : Nat → Nat) (Lf Li : Nat → Nat → Nat)
    (wd : List Int) (tgt : Nat → Nat) : Bool :=
  bAnd(lettersK kL wd, allN nb (fun s => strictB (B s) (fun b =>
    Nat.beq (wordPtK (letF Lf Li) wd b) (tgt b))))

@[expose] noncomputable def pairLf (w m P0 P1 rp rpi l y : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), pg w m P0 y, nIf(Nat.beq l (nat_lit 1), pg w m P1 y,
    nIf(Nat.beq l (nat_lit 2), pg w m rp (pg w m P0 (pg w m rpi y)),
      pg w m rp (pg w m P1 (pg w m rpi y)))))

@[expose] noncomputable def genLf (w m : Nat) (G : Nat → Nat) (l y : Nat) : Nat := pg w m (G l) y

end CFSG.KS.TitsOver

end
