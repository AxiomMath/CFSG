module

public import Certificates.Data.Kernel.OpsF2K
public import CFSG.RankThree.PartOne.CTP.FusionDefs
public import Certificates.Data.DoubleCoverRanks

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] noncomputable def evalWK (d : Nat) (R : List Nat) : Word → Nat
  | [] => idF d
  | (r, e) :: w => mulF d (powK d (getR d R r) e) (evalWK d R w)

@[expose] def wordLtK (n : Nat) (w : Word) : Bool :=
  w.all fun p => decide (p.1 < n) && decide (p.2 < 65536)

@[expose] noncomputable def factK (d : Nat) (R : List Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && decide (e < 65536) &&
      Nat.beq (powK d (getR d R r) e) (idF d)
  | .conj h u w => decide (h < n) && wordLtK n u && wordLtK n w &&
      Nat.beq (mulF d (getR d R h) (evalWK d R u)) (mulF d (evalWK d R w) (getR d R h))
  | .ne w₁ w₂ t => wordLtK n w₁ && wordLtK n w₂ && decide (t < d) &&
      !Nat.beq (vmF d (evalWK d R w₁) (pw2 t)) (vmF d (evalWK d R w₂) (pw2 t))
  | .eq w₁ w₂ => wordLtK n w₁ && wordLtK n w₂ && Nat.beq (evalWK d R w₁) (evalWK d R w₂)

@[expose] noncomputable def mcertK (d A B : Nat) (C : MCert) : Bool :=
  let R := runK d A B C.nregs C.prog
  seedsOK d A B && C.prog.all expOK && decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) &&
    C.facts.all (factK d R C.nregs)

@[expose] noncomputable def fusK (d A B nregs : Nat) (prog : List Op)
    (D : CFSG.RankThree.PartOne.CTP.Fus.Spec) : Bool :=
  let R := runK d A B nregs prog
  mcertK d A B ⟨nregs, prog, D.facts⟩ && decide (D.rA < nregs) && decide (D.rB < nregs) &&
    Nat.beq (getR d R D.rA) A && Nat.beq (getR d R D.rB) B && D.wf

open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
@[expose] noncomputable def e8K (d A B : Nat) (D : E8Data) : Bool :=
  let R := runK d A B D.nregs D.prog
  let X := getR d R D.rx
  let H := getR d R D.rh
  let H' := powK d H (D.oh - 1)
  let X₂ := mulF d (mulF d H X) H'
  let X₃ := mulF d (mulF d H X₂) H'
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    decide (D.rx < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.oh) &&
    decide (D.oh < 65536) && decide (D.t < d) &&
    Nat.beq (powK d X 2) (idF d) && Nat.beq (powK d H D.oh) (idF d) &&
    !Nat.beq (vmF d X (pw2 D.t)) (pw2 D.t) &&
    commK d X X₂ && commK d X X₃ && conjK d H X₃ (mulF d X X₂)

end CFSG.KC.OpsF2K

end
