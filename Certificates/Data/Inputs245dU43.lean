module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245d

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3

@[expose] def nregs : Nat := 11

@[expose] def cpProg : List Op :=
  [.pow 3 0 2, .pow 11 1 3, .pow 2 1 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .mul 4 3 4, .mul 4 0 4,
   .mul 4 3 4, .mul 4 3 4, .mul 4 0 4, .pow 3 1 5, .mul 4 5 5, .mul 0 4 6, .mul 6 3 6, .pow 3 6 7,
   .pow 2 5 8, .mul 5 7 9, .mul 9 8 9, .mul 8 7 10, .mul 10 5 10]

@[expose] def cpSpec : CpSpec where
  p := 3
  m :=
    { b0 := 7, b1 := 9, b2 := 10, w0 := [(7, 1)], w1 := [(9, 1)], w2 := [(10, 1)],
      indep := [(0, 0, 1, 0), (0, 0, 2, 0), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 2, 0), (0, 2, 0, 0),
        (0, 2, 1, 0), (0, 2, 2, 0), (1, 0, 0, 0), (1, 0, 1, 0), (1, 0, 2, 0), (1, 1, 0, 0),
        (1, 1, 1, 0), (1, 1, 2, 0), (1, 2, 0, 0), (1, 2, 1, 0), (1, 2, 2, 0), (2, 0, 0, 0),
        (2, 0, 1, 0), (2, 0, 2, 0), (2, 1, 0, 0), (2, 1, 1, 0), (2, 1, 2, 0), (2, 2, 0, 0),
        (2, 2, 1, 0), (2, 2, 2, 0)],
      acts := [{ reg := 0, ord := 4, mat := [0, 1, 2, 1, 0, 2, 0, 0, 2] },
        { reg := 5, ord := 3, mat := [0, 0, 1, 1, 0, 0, 0, 1, 0] }] }
  pts :=
    [{ reg := 7, w := [(7, 1)], t := 0, hs := [{ reg := 1, ord := 12, e := 1 }] }]
  rA := 0
  oA := 4
  rB := 1
  oB := 12
  wA := [(0, 1)]
  wB := [(1, 1)]

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245d
