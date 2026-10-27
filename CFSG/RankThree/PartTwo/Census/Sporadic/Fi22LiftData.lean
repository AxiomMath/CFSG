module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22W4Data
public import Certificates.Data.TripleCoverLift.Check

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.SectionRank.Native

@[expose] def fi22LiftExtra : List Op := [.mul 299 758 759, .mul 186 755 760, .mul 760 186 761]

@[expose] def fi22Lift : LiftData where
  base :=
    { seedA := include_str "../../../../Blueprint/Data/F22G1-f3r77B0.m1"
      seedB := include_str "../../../../Blueprint/Data/F22G1-f3r77B0.m2"
      nregs := 762
      prog := fi22W4Prog0 ++ fi22W4Prog1 ++ fi22LiftExtra
      outs := [758, 753, 748, 759]
      tests := [0] }
  inv₁ := 0
  inv₂ := 0
  units := [(755, 2), (750, 2), (591, 2), (761, 2), (652, 2), (186, 2), (571, 2), (527, 2)]
  rels := [.inv 755 0, .inv 750 1, .inv 591 2, .inv 761 3, .fix 750 0, .fix 591 1,
    .swap 652 0 2, .swap 186 0 3, .swap 571 1 3, .swap 527 2 3]

end CFSG.RankThree.PartTwo.Census
