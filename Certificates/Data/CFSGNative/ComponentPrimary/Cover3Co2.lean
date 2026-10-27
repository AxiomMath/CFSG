module

public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3

public section

namespace CFSG.SectionRank.Native

@[expose] def co2Max10Cover3 : Cover3Data Nat where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
  m := 3
  nregs := 8
  prog := [.mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 6, 
      .mul 2 6 2, .mul 4 6 6, .pow 5 6 6, .pow 3 4 4, .pow 17 5 5, .pow 24 2 2, 
      .mul 5 2 5, .pow 7 5 2, .mul 2 4 2, .mul 2 5 2, .pow 7 2 5, .mul 2 6 4, 
      .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 5 4, .mul 4 6 4, .mul 4 5 4, 
      .mul 4 2 4, .mul 4 5 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, .mul 4 5 4, 
      .mul 4 6 4, .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, 
      .mul 4 5 4, .mul 4 6 4, .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 5 4, 
      .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 5 4, .mul 4 6 4, .mul 4 2 4, 
      .mul 4 5 4, .mul 4 6 4, .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 2 4, 
      .mul 4 2 4, .mul 4 2 4, .mul 4 2 4, .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, 
      .mul 4 5 4, .mul 4 2 4, .mul 4 5 4, .mul 4 5 4, .mul 6 6 3, .mul 3 6 3, 
      .mul 3 5 3, .mul 3 2 3, .mul 3 6 3, .mul 3 6 3, .mul 3 6 3, .mul 3 2 3, 
      .mul 3 2 3, .mul 3 6 3, .mul 3 2 3, .mul 3 5 3, .mul 3 2 3, .mul 3 2 3, 
      .mul 3 6 3, .mul 3 6 3, .mul 3 2 3, .mul 3 6 3, .mul 3 6 3, .mul 3 5 3, 
      .mul 3 6 3, .mul 3 5 3, .mul 3 5 3, .mul 3 2 3, .mul 3 2 3, .mul 3 5 3, 
      .mul 3 6 3, .mul 3 6 3, .mul 3 5 3, .mul 3 6 3, .mul 3 5 3, .mul 3 6 3, 
      .mul 3 2 3, .mul 3 6 3, .mul 3 2 3, .mul 3 2 3, .mul 3 5 3, .mul 3 2 3, 
      .mul 3 6 3, .mul 3 6 3, .mul 3 6 3, .mul 3 6 3, .mul 3 6 3, .mul 3 6 3, 
      .mul 3 6 3, .mul 3 6 3, .mul 3 2 3, .mul 3 6 3, .mul 3 5 3, .mul 3 2 3, 
      .mul 3 6 3, .mul 3 6 3, .mul 2 6 7, .mul 7 6 7, .mul 7 5 7, .mul 7 6 7, 
      .mul 7 5 7, .mul 7 2 7, .mul 7 6 7, .mul 7 6 7, .mul 7 6 7, .mul 7 6 7, 
      .mul 7 6 7, .mul 7 6 7, .mul 7 2 7, .mul 7 6 7, .mul 7 5 7, .mul 7 2 7, 
      .mul 7 5 7, .mul 7 6 7, .mul 7 6 7, .mul 7 6 7, .mul 7 6 7, .mul 7 2 7, 
      .mul 7 6 7, .mul 7 6 7, .mul 7 6 7, .mul 7 2 7, .mul 7 2 7, .mul 7 2 7, 
      .mul 7 5 7, .mul 7 5 7, .mul 7 6 7]
  regs := [4, 3, 7]
  ordv := [10, 8, 4]
  ord := [10, 8, 4]
  relCodes := [[4, 2, 4, 4, 2, 4, 3, 4, 3, 3, 5, 2],
    [2, 4, 4, 2, 2, 2, 4, 2, 4, 2, 2, 5, 2, 5],
    [2, 4, 4, 2, 2, 4, 4, 2, 2, 2, 4, 2, 2, 4],
    [2, 2, 2, 4, 4, 2, 4, 4, 2, 2, 4, 2, 2, 4],
    [2, 1, 5, 3, 0, 4, 4, 2, 4, 1, 2, 1],
    [4, 0, 3, 4, 4, 2, 5, 3, 4, 0, 3, 0],
    [4, 2, 5, 3, 3, 3, 5, 3, 4, 2, 2, 2],
    [4, 4, 2, 1, 5, 1, 2, 1, 5, 2, 4, 3],
    [4, 1, 2, 1, 2, 1, 5, 3, 0, 5, 5, 2],
    [2, 2, 2, 4, 2, 4, 1, 3, 0, 5, 3, 1, 1]]
  commCodes := [[], [], []]
  starts := [2611232, 1384336]
  tree := include_str "Co2Cover3.tree"

end CFSG.SectionRank.Native
