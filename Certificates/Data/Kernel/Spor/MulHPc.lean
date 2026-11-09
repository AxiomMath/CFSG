module

public import Certificates.Data.Kernel.Spor.MulHQI
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Prim

@[expose] noncomputable def pcNK (T P : Nat → Nat) (i : Nat) : Nat := T (r32 P i)

@[expose] noncomputable def pcTK (n w m : Nat) (T P : Nat → Nat) (r i : Nat) : Bool :=
  strictB (Nat.shiftLeft (nat_lit 1) r) (fun e => Nat.beq (pcNK T P (Nat.add e i))
    (pcomp n w m (pcNK T P i) (pcNK T P e)))

@[expose] noncomputable def pcRK (n w m K : Nat) (T P A B : Nat → Nat) (r lo len : Nat) : Bool :=
  strictB (Nat.shiftLeft (nat_lit 1) r) (fun e => strictB (pcNK T P e) (fun y =>
    bAnd(canonK n w m (Nat.mul n w) y, strictB (r32 A r) (fun a => bAnd(Nat.blt a e,
      bAnd(Nat.beq (pcomp n w m y y) (pcNK T P a),
      allN len (fun d => strictB (Nat.add lo d) (fun s => bIf(Nat.blt s r,
        strictB (r32 B (Nat.add (Nat.mul r K) s)) (fun b => bAnd(Nat.blt b e,
          Nat.beq (pcomp n w m y (pcNK T P (Nat.shiftLeft (nat_lit 1) s)))
            (pcomp n w m (pcNK T P b) y))), true)))))))))

@[expose] noncomputable def pcMK (n w m k cnt p : Nat) (T G P S U PP : Nat → Nat) : Bool :=
  bAnd(Nat.beq (pcNK T P 0) (pidn n w), bAnd(canonK n w m (Nat.mul n w) (pcNK T P 0),
  bAnd(allN cnt (fun i => bAnd(Nat.blt (r32 P i) cnt, strictB (r32 S i) (fun s =>
    bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 P s) i, Nat.beq (pg w m (PP 0) (pg w m (T i) p)) i))))),
  allN k (fun j => strictB (r32 U j) (fun u => bAnd(Nat.blt u cnt, Nat.beq (G j) (pcNK T P u)))))))

@[expose] noncomputable def pcCK (w m k cnt p : Nat) (T G CL : Nat → Nat) (c : Nat) : Bool :=
  bIf(Nat.blt (Nat.mod c (Nat.add k k)) k,
    strictB (r32 CL c) (fun q => bAnd(Nat.blt q cnt, Nat.beq (pg w m (T q) p)
      (pg w m (T (Nat.div c (Nat.add k k))) (pg w m (G (Nat.mod c (Nat.add k k))) p)))),
    invIxK k cnt CL c)

end CFSG.KS.MulH

end
