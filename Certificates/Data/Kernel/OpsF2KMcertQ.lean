module

public import Certificates.Data.Kernel.OpsF2KQ

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Misc.G24 (mulF2)

@[expose] noncomputable def mcertQ (d A B : Nat) (C : MCert) : Bool :=
  let R := runQ d A B C.nregs C.prog
  seedsOK d A B && C.prog.all expOK && decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) &&
    C.facts.all (factQ d R C.nregs)

open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
@[expose] noncomputable def e8Q (d A B : Nat) (D : E8Data) : Bool :=
  let R := runQ d A B D.nregs D.prog
  let X := getR d R D.rx
  let H := getR d R D.rh
  let H' := pqK d H (D.oh - 1)
  let X₂ := mulF2 d (mulF2 d H X) H'
  let X₃ := mulF2 d (mulF2 d H X₂) H'
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    decide (D.rx < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.oh) &&
    decide (D.oh < 65536) && decide (D.t < d) &&
    Nat.beq (pqK d X 2) (idF d) && Nat.beq (pqK d H D.oh) (idF d) &&
    !Nat.beq (vmF d X (pw2 D.t)) (pw2 D.t) &&
    commQ d X X₂ && commQ d X X₃ && conjQ d H X₃ (mulF2 d X X₂)

end CFSG.KC.OpsF2K

end
