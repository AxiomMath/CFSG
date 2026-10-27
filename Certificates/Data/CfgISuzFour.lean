module

public import Certificates.Data.TripleCoverSuz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.SuzFour.Native

open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.Native

@[expose] def wordY4 : List (Nat × Bool) :=
  [(1, true), (0, true), (2, true), (1, true), (0, true), (1, true), (2, true), (1, true),
    (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (0, true), (5, true),
    (1, true), (0, true), (1, true), (2, true), (3, true), (2, true), (0, true), (6, true),
    (1, true), (2, true), (3, true), (0, true), (1, true), (2, true), (1, true)]

@[expose] def wordN4 : List (Nat × Bool) :=
  [(5, true), (1, true), (6, true), (1, true), (0, true), (1, true), (0, true), (2, true),
    (1, true), (5, true), (2, true), (3, true), (1, true), (2, true), (3, true), (0, true),
    (1, true), (1, true), (2, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (0, true), (3, true), (2, true), (1, true), (3, true), (2, true), (3, true),
    (2, true), (1, true), (0, true), (1, true), (2, true), (3, true), (0, true), (1, true),
    (2, true), (1, true), (0, true)]

@[expose] noncomputable def nY4 : Nat := wordN wordY4

@[expose] noncomputable def nN4 : Nat := wordN wordN4

@[expose] noncomputable def cfg4OK : Bool :=
  Nat.beq (comp nY4 (sqN nY4)) pid &&
    Nat.beq (comp nY1 nY4) (comp nY4 nY1) && Nat.beq (comp nY2 nY4) (comp nY4 nY2) &&
    Nat.beq (comp nY3 nY4) (comp nY4 nY3) &&
    Nat.beq (comp nN4 nY4) (comp (sqN nY4) nN4) &&
    Nat.beq (comp nN4 nY1) (comp nY1 nN4) && Nat.beq (comp nN4 nY2) (comp nY2 nN4) &&
    Nat.beq (comp nN4 nY3) (comp nY3 nN4) &&
    !(Nat.beq (ent nY1 0) 0) && !(Nat.beq (ent nY2 0) 0) && !(Nat.beq (ent nY3 0) 0) &&
    !(Nat.beq (ent nY4 0) 0)

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.SuzFour.Native
