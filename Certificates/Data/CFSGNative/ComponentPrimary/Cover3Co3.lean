module

public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3

public section

namespace CFSG.SectionRank.Native


@[expose] def co3Max8Cover3 : Cover3Data Nat where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
  m := 3
  nregs := 8
  prog := [.mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 0 5 5, .pow 11 5 5, 
      .pow 4 3 3, .pow 5 2 2, .pow 11 4 4, .mul 2 4 2, .pow 11 2 4, .mul 4 3 4, 
      .mul 4 2 4, .pow 5 4 2, .mul 2 4 3, .mul 3 4 3, .mul 3 2 3, .mul 3 2 3, 
      .mul 3 5 3, .mul 3 5 3, .mul 3 5 3, .mul 3 2 3, .mul 3 2 3, .mul 3 4 3, 
      .mul 3 5 3, .mul 3 2 3, .mul 3 5 3, .mul 3 2 3, .mul 3 5 3, .mul 3 5 3, 
      .mul 3 2 3, .mul 3 4 3, .mul 3 5 3, .mul 3 5 3, .mul 3 5 3, .mul 3 2 3, 
      .mul 3 5 3, .mul 3 5 3, .mul 3 5 3, .mul 3 5 3, .mul 3 2 3, .mul 3 2 3, 
      .mul 3 4 3, .mul 3 2 3, .mul 3 4 3, .mul 3 2 3, .mul 3 2 3, .mul 3 5 3, 
      .mul 3 2 3, .mul 3 5 3, .mul 3 4 3, .mul 3 5 3, .mul 3 2 3, .mul 3 4 3, 
      .mul 3 5 3, .mul 3 2 3, .mul 3 5 3, .mul 3 5 3, .mul 3 5 3, .mul 3 5 3, 
      .mul 3 5 3, .mul 3 2 3, .mul 3 4 3, .mul 3 5 3, .mul 3 5 3, .mul 2 5 6, 
      .mul 6 5 6, .mul 6 4 6, .mul 6 5 6, .mul 6 2 6, .mul 6 2 6, .mul 6 2 6, 
      .mul 6 2 6, .mul 6 2 6, .mul 6 5 6, .mul 6 4 6, .mul 6 5 6, .mul 6 5 6, 
      .mul 6 2 6, .mul 6 5 6, .mul 6 5 6, .mul 6 5 6, .mul 6 5 6, .mul 6 5 6, 
      .mul 6 5 6, .mul 6 5 6, .mul 6 2 6, .mul 6 5 6, .mul 6 4 6, .mul 6 5 6, 
      .mul 6 5 6, .mul 6 2 6, .mul 6 5 6, .mul 6 4 6, .mul 6 5 6, .mul 6 4 6, 
      .mul 6 5 6, .mul 6 5 6, .mul 6 2 6, .mul 6 2 6, .mul 6 5 6, .mul 6 2 6, 
      .mul 6 5 6, .mul 6 2 6, .mul 6 4 6, .mul 6 4 6, .mul 6 5 6, .mul 6 5 6, 
      .mul 6 5 6, .mul 5 5 7, .mul 7 4 7, .mul 7 4 7, .mul 7 4 7, .mul 7 5 7, 
      .mul 7 5 7, .mul 7 2 7, .mul 7 2 7, .mul 7 5 7, .mul 7 5 7, .mul 7 5 7, 
      .mul 7 2 7, .mul 7 4 7, .mul 7 5 7, .mul 7 5 7, .mul 7 4 7, .mul 7 4 7, 
      .mul 7 5 7, .mul 7 5 7, .mul 7 2 7, .mul 7 4 7, .mul 7 5 7, .mul 7 2 7, 
      .mul 7 2 7, .mul 7 2 7, .mul 7 5 7, .mul 7 4 7, .mul 7 4 7, .mul 7 5 7, 
      .mul 7 5 7, .mul 7 5 7, .mul 7 4 7, .mul 7 4 7, .mul 7 4 7, .mul 7 2 7, 
      .mul 7 5 7, .mul 7 5 7, .mul 7 4 7, .mul 7 5 7, .mul 7 5 7, .mul 7 2 7, 
      .mul 7 2 7, .mul 7 2 7, .mul 7 5 7, .mul 7 5 7, .mul 7 4 7, .mul 7 5 7, 
      .mul 7 5 7, .mul 7 2 7, .mul 7 5 7, .mul 7 4 7]
  regs := [3, 6, 7]
  ordv := [8, 8, 4]
  ord := [8, 8, 4]
  relCodes := [[2, 4, 2, 2, 4, 2, 2, 4, 2, 2, 4, 2],
    [4, 2, 2, 4, 2, 4, 4, 2, 2, 4, 2, 4],
    [4, 2, 2, 4, 4, 4, 2, 4, 4, 2, 2, 5, 2, 4],
    [4, 2, 2, 4, 2, 2, 4, 4, 2, 2, 2, 2, 5, 3, 4, 3],
    [2, 4, 4, 2, 4, 4, 2, 4, 2, 2, 5, 3, 3, 5, 3, 5],
    [2, 2, 1, 1, 4, 2, 0, 0, 2, 4],
    [4, 1, 4, 1, 4, 1, 4, 1, 4, 1],
    [4, 0, 5, 3, 1, 3, 1, 2, 5, 0, 5, 3],
    [2, 4, 2, 2, 4, 4, 1, 5, 2, 5, 5, 1],
    [2, 1, 2, 5, 2, 0, 3, 0, 3, 4, 2, 1],
    [4, 2, 0, 3, 5, 0, 5, 2, 4, 3, 3, 3]]
  commCodes := [[], [], []]
  starts := [2611232, 1384336]
  tree := include_str "Co3Max8Cover3.tree"

end CFSG.SectionRank.Native
