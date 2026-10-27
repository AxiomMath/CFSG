module

public import Certificates.Data.Kernel.OpsLayK
public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] noncomputable def evalWL (c : Lay) (R : List Nat) : Word → Nat
  | [] => c.ONE
  | (r, e) :: w => c.mul (powK c (getR c R r) e) (evalWL c R w)

@[expose] def wordOK (n : Nat) (w : Word) : Bool :=
  w.all fun p => decide (p.1 < n) && decide (p.2 < 65536)

@[expose] noncomputable def factL (c : Lay) (R : List Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && decide (e < 65536) &&
      Nat.beq (powK c (getR c R r) e) c.ONE
  | .conj h u w => decide (h < n) && wordOK n u && wordOK n w &&
      Nat.beq (c.mul (getR c R h) (evalWL c R u)) (c.mul (evalWL c R w) (getR c R h))
  | .ne w₁ w₂ t => wordOK n w₁ && wordOK n w₂ && decide (t < c.d) &&
      !Nat.beq (c.vec (c.unit t) (evalWL c R w₁)) (c.vec (c.unit t) (evalWL c R w₂))
  | .eq w₁ w₂ => wordOK n w₁ && wordOK n w₂ && Nat.beq (evalWL c R w₁) (evalWL c R w₂)

@[expose] noncomputable def mcertL (c : Lay) (A B : Nat) (C : MCert) : Bool :=
  progOK C.nregs C.prog &&
    runC c C.prog (initR c A B C.nregs) fun R => C.facts.all (factL c R C.nregs)

@[expose] noncomputable def seedsL (c : Lay) (A B : Nat) (C : MCert) (rA rB : Nat) : Bool :=
  progOK C.nregs C.prog && decide (rA < C.nregs) && decide (rB < C.nregs) &&
    runC c C.prog (initR c A B C.nregs) fun R => C.facts.all (factL c R C.nregs) &&
      Nat.beq (getR c R rA) A && Nat.beq (getR c R rB) B

@[expose] def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && eqL as bs
  | _, _ => false

@[expose] noncomputable def chunkL (c : Lay) (prog : List Op) (k i : Nat) (R S : List Nat) :
    Bool :=
  runC c ((prog.drop (i * k)).take k) R fun R' => eqL R' S

@[expose] noncomputable def factsL (c : Lay) (R : List Nat) (n : Nat) (fs : List MFact)
    (k i : Nat) : Bool :=
  ((fs.drop (i * k)).take k).all (factL c R n)

@[expose] def seedRegsL (c : Lay) (R : List Nat) (A B rA rB : Nat) : Bool :=
  Nat.beq (getR c R rA) A && Nat.beq (getR c R rB) B

end CFSG.KC.OpsLayK

end
