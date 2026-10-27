module

public import Certificates.Data.Kernel.Misc.YamakiA0
public import Certificates.Data.Sp62RecCR1CE
public import Certificates.Data.Kernel.Misc.YamakiRepF
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KD.YamakiCE

open CFSG.KD.BfsK CFSG.KD.YamakiA0 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Sp62Rec
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def numPosK (R : Nat → Nat) (o n : Nat) : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, p :: ps => Nat.blt p n && Nat.beq (recX R o p) x && numPosK R o n xs ps

@[expose] noncomputable def memK (R : Nat → Nat) (o n x : Nat) : Bool :=
  (List.range n).any fun p => Nat.beq (recX R o p) x

@[expose] noncomputable def sqK (R : Nat → Nat) (o n : Nat) : Bool :=
  (List.range n).all fun t => Nat.beq (MULF (recX R o t) (recX R o t)) ONE

@[expose] noncomputable def v0ConjK (R : Nat → Nat) (o : Nat) : Bool :=
  idxHhat.all fun s => v0Idx.all fun i => memK R o 32 (MULF (MULF (R s) (R i)) (R s))

@[expose] noncomputable def commGkK (R : Nat → Nat) (o : Nat) : Bool :=
  (List.range 5).all fun k => memK R o 32 (wordN R (commGWords.getD k []))

@[expose] noncomputable def fixK (R : Nat → Nat) (ws : List (List Nat)) (x : Nat) : Bool :=
  ws.all fun w => Nat.beq (MULF (wordN R w) x) (MULF x (wordN R w))

@[expose] noncomputable def commFixK (R : Nat → Nat) (o : Nat) (ws : List (List Nat)) : Bool :=
  fixK R ws (wordN R commV1) && (List.range 32).all fun t => !(fixK R ws (recX R o t)) ||
    (Nat.beq (recX R o t) ONE || Nat.beq (recX R o t) (wordN R commV1) ||
      Nat.beq (recX R o t) (R 5) || Nat.beq (recX R o t) (MULF (wordN R commV1) (R 5)))

@[expose] noncomputable def commTripleK (R : Nat → Nat) : Bool :=
  !(Nat.beq (wordN R commV1) ONE) && !(Nat.beq (R 5) ONE) &&
    !(Nat.beq (wordN R (conjWord (commTriple.getD 0 []) commV1)) (wordN R commV1)) &&
    Nat.beq (MULF (wordN R (conjWord (commTriple.getD 0 []) commV1))
      (wordN R (conjWord (commTriple.getD 1 []) commV1)))
      (wordN R (conjWord (commTriple.getD 2 []) commV1))

@[expose] noncomputable def wordG (g : Nat → Nat) : List Nat → Nat
  | [] => ONE
  | k :: w => MULF (g k) (wordG g w)

@[expose] noncomputable def commExprK (R : Nat → Nat) : Bool :=
  (List.range 5).all fun i => ((commExpr.getD i []).all fun k => decide (k < 5)) &&
    Nat.beq (wordG (fun k => wordN R (commGWords.getD k [])) (commExpr.getD i []))
      (R (v0Idx.getD i 0))

@[expose] noncomputable def centAt (e1 e2 a x : Nat) : Bool :=
  !(Nat.beq (MULF x e1) (MULF e1 x) && Nat.beq (MULF x e2) (MULF e2 x)) || Nat.beq x ONE ||
    Nat.beq x a

@[expose] noncomputable def centChunk (R : Nat → Nat) (o n L q ai : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (wordN R (e0Words.getD 0 [])) fun e1 =>
  CFSG.KD.YamakiRepF.strictY (wordN R (e0Words.getD 1 [])) fun e2 =>
  CFSG.KD.YamakiRepF.strictY (R ai) fun a =>
    CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
      cond (Nat.blt t n) (CFSG.KD.YamakiRepF.strictY (recX R o t) fun x => centAt e1 e2 a x) true

end CFSG.KD.YamakiCE

end
