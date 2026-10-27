module

public import CFSG.RankThree.PartOne.SEITZQ1.AmbientPlane
public import CFSG.RankThree.PartOne.SEITZQ1.Consumer

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Final


theorem phi2Ambient_of_card {m : ℕ} (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) : Phi2Ambient m K := by
  intro p hp hp5 hpq
  exact q1_phi2_plane hm hK hp hp5 hpq

theorem exc2F4NonsplitPhi2_holds :
    CFSG.RankThree.PartOne.SEITZ2.Exc2F4NonsplitPhi2 :=
  exc2F4NonsplitPhi2_of_ambient fun _ K _ _ _ hm hK => phi2Ambient_of_card hm K hK

end Final

end CFSG.RankThree.PartOne.SEITZQ1
