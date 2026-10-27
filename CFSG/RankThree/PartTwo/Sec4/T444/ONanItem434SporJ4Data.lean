module

public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4ThreeData

public section

namespace CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

@[expose] def j4ExtProg : List Op :=
  [.mul 146 438 797, .mul 797 643 798, .mul 798 643 799, .mul 146 648 800, .pow 7 438 801,
   .mul 800 801 802, .pow 2 285 803, .mul 802 803 804, .pow 5 643 805, .pow 7 438 806,
   .mul 805 806 807, .pow 5 643 808, .mul 807 808 809, .mul 809 146 810, .pow 3 767 811,
   .pow 5 643 812, .mul 438 812 813, .mul 813 651 814, .mul 814 767 815, .mul 767 815 816,
   .mul 146 285 817, .pow 2 285 818, .mul 146 818 819]

@[expose] def j4Prog : List Op := CoreJ43.prog ++ j4ExtProg

@[expose] def j4Nregs : Nat := 820

@[expose] def j4Spec : FixSpec where
  rA := 0
  oA := 2
  rB := 1
  oB := 4
  rx := 146
  ry := 285
  rz := 290
  tz := 0
  rxy := 817
  rxy2 := 819
  gens :=
    [{ reg := 799, ord := 4, u := [(146, 1)], tu := 0 },
     { reg := 804, ord := 4, u := [(290, 1), (146, 1)], tu := 0 },
     { reg := 810, ord := 4, u := [(290, 1)], tu := 0 },
     { reg := 811, ord := 4, u := [(290, 1)], tu := 0 }]
  ders :=
    [{ reg := 146, ord := 3,
       w := [(810, 1), (799, 1), (810, 1), (799, 1), (810, 1), (804, 1), (799, 1), (804, 1)] },
     { reg := 285, ord := 3, w := [(810, 1), (799, 1), (810, 1), (799, 1)] },
     { reg := 290, ord := 3,
       w := [(804, 1), (810, 1), (799, 1), (810, 1), (799, 1), (810, 1), (804, 1), (799, 1)] },
     { reg := 438, ord := 8,
       w := [(804, 1), (810, 1), (799, 1), (804, 1), (810, 1), (799, 1), (810, 1)] },
     { reg := 643, ord := 6, w := [(799, 1), (810, 1), (804, 1), (799, 1)] },
     { reg := 648, ord := 2,
       w := [(804, 1), (810, 1), (799, 2), (804, 1), (810, 1), (804, 1), (810, 1)] },
     { reg := 651, ord := 2, w := [(799, 2)] },
     { reg := 652, ord := 2, w := [(799, 2), (810, 2)] },
     { reg := 787, ord := 2, w := [(651, 1), (652, 1)] },
     { reg := 767, ord := 12, w := [(290, 2), (811, 3)] },
     { reg := 768, ord := 12, w := [(767, 11)] },
     { reg := 770, ord := 3, w := [(767, 1), (146, 1), (768, 1)] },
     { reg := 772, ord := 3, w := [(767, 1), (285, 1), (768, 1)] },
     { reg := 774, ord := 8, w := [(767, 1), (438, 1), (768, 1)] },
     { reg := 776, ord := 6, w := [(767, 1), (643, 1), (768, 1)] },
     { reg := 780, ord := 2, w := [(767, 1), (651, 1), (768, 1)] },
     { reg := 782, ord := 2, w := [(767, 1), (652, 1), (768, 1)] },
     { reg := 790, ord := 3, w := [(772, 1), (770, 2), (780, 1)] },
     { reg := 793, ord := 2, w := [(774, 4)] },
     { reg := 796, ord := 20, w := [(774, 4), (438, 5)] }]
  wA := CoreJ43.spec.wA
  wB := CoreJ43.spec.wB
  c1 :=
    { reg := 767, ord := 12,
      wz := [(290, 1)],
      wx := [(290, 2), (819, 2)] }
  c2 :=
    { reg := 815, ord := 8,
      wz := [(290, 2)],
      wx := [(290, 2), (817, 2)] }
  c3 :=
    { reg := 816, ord := 2,
      wz := [(290, 2)],
      wx := [(290, 2), (285, 1)] }

end CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine
