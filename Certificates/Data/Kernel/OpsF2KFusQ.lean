module

public import Certificates.Data.Kernel.OpsF2KMcert
public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KC.Loop CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Misc.G24 (mulF2)

@[expose] noncomputable def pqF (d : Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => idF d)
    (fun _ ih X e => nIf(Nat.beq e 0, idF d, nIf(Nat.beq e 1, X,
      strictN (mulF2 d X X) fun S => strictN (ih S (Nat.shiftRight e 1)) fun Y =>
        nIf(Nat.beq (Nat.land e 1) 1, mulF2 d X Y, Y)))) n

@[expose] noncomputable def pqK (d X e : Nat) : Nat := pqF d 16 X e

@[expose] noncomputable def stepQ (d : Nat) (R : List Nat) : Op → List Nat
  | .mul i j k => R.set k (mulF2 d (getR d R i) (getR d R j))
  | .pow e i k => R.set k (pqK d (getR d R i) e)

@[expose] noncomputable def runQ (d A B n : Nat) (prog : List Op) : List Nat :=
  prog.foldl (stepQ d) ((List.range n).map fun r => if r = 0 then A else if r = 1 then B else idF d)

@[expose] noncomputable def evalWQ (d : Nat) (R : List Nat) : Word → Nat :=
  List.rec (motive := fun _ => Nat) (idF d) fun p w ih =>
    nIf(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) w,
      pqK d (getR d R p.1) p.2, mulF2 d (pqK d (getR d R p.1) p.2) ih)

@[expose] noncomputable def factQ (d : Nat) (R : List Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && decide (e < 65536) &&
      Nat.beq (pqK d (getR d R r) e) (idF d)
  | .conj h u w => decide (h < n) && wordLtK n u && wordLtK n w &&
      Nat.beq (mulF2 d (getR d R h) (evalWQ d R u)) (mulF2 d (evalWQ d R w) (getR d R h))
  | .ne w₁ w₂ t => wordLtK n w₁ && wordLtK n w₂ && decide (t < d) &&
      !Nat.beq (vmF d (evalWQ d R w₁) (pw2 t)) (vmF d (evalWQ d R w₂) (pw2 t))
  | .eq w₁ w₂ => wordLtK n w₁ && wordLtK n w₂ && Nat.beq (evalWQ d R w₁) (evalWQ d R w₂)

@[expose] noncomputable def fusQ (d A B nregs : Nat) (prog : List Op)
    (D : CFSG.RankThree.PartOne.CTP.Fus.Spec) : Bool :=
  let R := runQ d A B nregs prog
  seedsOK d A B && prog.all expOK && decide (2 ≤ nregs) && prog.all (Op.lt nregs) &&
    D.facts.all (factQ d R nregs) && decide (D.rA < nregs) && decide (D.rB < nregs) &&
    Nat.beq (getR d R D.rA) A && Nat.beq (getR d R D.rB) B && D.wf

end CFSG.KC.OpsF2K

end
