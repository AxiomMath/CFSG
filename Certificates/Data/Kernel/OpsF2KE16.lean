module

public import Certificates.Data.Kernel.OpsF2KMcert
public import Certificates.Data.SporadicTwoCover

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native

@[expose] noncomputable def e16K (d A B : Nat) (D : E8Data) : Bool :=
  let R := runK d A B D.nregs D.prog
  let X := getR d R D.rx
  let H := getR d R D.rh
  let H' := powK d H (D.oh - 1)
  let X₂ := mulF d (mulF d H X) H'
  let X₃ := mulF d (mulF d H X₂) H'
  let X₄ := mulF d (mulF d H X₃) H'
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    decide (D.rx < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.oh) &&
    decide (D.oh < 65536) && decide (D.t < d) &&
    Nat.beq (powK d X 2) (idF d) && Nat.beq (powK d H D.oh) (idF d) &&
    !Nat.beq (vmF d X (pw2 D.t)) (pw2 D.t) &&
    commK d X X₂ && commK d X X₃ && commK d X X₄ && conjK d H X₄ (mulF d X X₂)

end CFSG.KC.OpsF2K
