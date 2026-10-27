module

public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3

public section

namespace CFSG.SectionRank.Native

@[expose] def thMax6Cover3 : Cover3Data (Nat) where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  m := 3
  nregs := 8
  prog := [.mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 4, .mul 4 3 4, .mul 2 2 5, 
      .mul 5 4 5, .pow 3 5 5, .pow 8 2 4, .pow 6 3 6, .mul 4 6 4, .pow 6 4 6, 
      .mul 6 0 6, .mul 6 4 6, .pow 13 3 3, .pow 5 2 2, .mul 3 2 3, .pow 12 3 2, 
      .mul 2 5 2, .mul 2 3 2, .pow 7 2 3, .mul 6 3 5, .mul 5 2 5, .mul 5 6 5, 
      .mul 5 3 5, .mul 5 2 5, .mul 5 6 5, .mul 5 6 5, .mul 5 6 5, .mul 5 6 5, 
      .mul 5 6 5, .mul 5 6 5, .mul 5 6 5, .mul 5 2 5, .mul 5 6 5, .mul 5 3 5, 
      .mul 5 3 5, .mul 5 2 5, .mul 5 2 5, .mul 5 6 5, .mul 5 6 5, .mul 5 6 5, 
      .mul 5 6 5, .mul 5 6 5, .mul 5 3 5, .mul 5 6 5, .mul 5 3 5, .mul 5 6 5, 
      .mul 5 6 5, .mul 5 3 5, .mul 5 2 5, .mul 5 3 5, .mul 5 6 5, .mul 5 3 5, 
      .mul 5 2 5, .mul 5 6 5, .mul 5 3 5, .mul 5 2 5, .mul 5 6 5, .mul 5 6 5, 
      .mul 5 6 5, .mul 5 6 5, .mul 6 6 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, 
      .mul 4 3 4, .mul 4 6 4, .mul 4 6 4, .mul 4 3 4, .mul 4 6 4, .mul 4 6 4, 
      .mul 4 2 4, .mul 4 2 4, .mul 4 2 4, .mul 4 6 4, .mul 4 3 4, .mul 4 2 4, 
      .mul 4 6 4, .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, .mul 4 3 4, 
      .mul 4 6 4, .mul 4 6 4, .mul 4 2 4, .mul 4 2 4, .mul 4 3 4, .mul 4 6 4, 
      .mul 4 2 4, .mul 4 6 4, .mul 4 6 4, .mul 4 2 4, .mul 4 2 4, .mul 4 3 4, 
      .mul 4 2 4, .mul 4 6 4, .mul 4 3 4, .mul 4 2 4, .mul 4 2 4, .mul 4 6 4, 
      .mul 4 6 4, .mul 4 3 4, .mul 4 3 4, .mul 4 2 4, .mul 4 2 4, .mul 4 2 4, 
      .mul 4 6 4, .mul 4 6 4, .mul 4 3 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, 
      .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, .mul 4 2 4, .mul 2 6 7, .mul 7 6 7, 
      .mul 7 6 7, .mul 7 6 7, .mul 7 2 7, .mul 7 2 7, .mul 7 6 7, .mul 7 3 7, 
      .mul 7 2 7, .mul 7 3 7, .mul 7 6 7, .mul 7 6 7, .mul 7 2 7, .mul 7 2 7, 
      .mul 7 3 7, .mul 7 6 7, .mul 7 6 7, .mul 7 6 7, .mul 7 2 7, .mul 7 3 7]
  regs := [5, 4, 7]
  ordv := [4, 2, 8]
  ord := [4, 2, 8]
  relCodes := [[5, 2, 4, 2, 1, 2, 5, 2, 4, 2, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 0, 3],
    [5, 2, 4, 2, 1, 5, 2, 4, 2, 4, 2, 4, 3, 0, 3, 0, 3, 1, 1, 3, 1, 3],
    [5, 2, 4, 2, 5, 2, 1, 2, 0, 2, 4, 0, 3, 5, 1, 3, 5, 3, 0, 3, 1, 3],
    [5, 2, 5, 2, 0, 0, 2, 0, 2, 5, 2, 5, 1, 3, 0, 3, 1, 3, 5, 3, 5, 3],
    [5, 2, 5, 2, 0, 2, 0, 0, 2, 5, 2, 0, 3, 1, 1, 3, 5, 3, 0, 3, 5, 1],
    [5, 2, 5, 2, 0, 2, 4, 2, 1, 2, 0, 4, 3, 4, 3, 5, 1, 3, 5, 3, 5, 3],
    [5, 2, 5, 2, 1, 2, 1, 5, 2, 0, 2, 5, 3, 5, 1, 3, 4, 3, 5, 3, 5, 3],
    [5, 2, 5, 2, 4, 2, 0, 0, 2, 0, 4, 1, 1, 3, 4, 3, 0, 3, 1, 1, 3, 5],
    [5, 2, 5, 2, 4, 2, 4, 2, 1, 2, 4, 3, 5, 1, 3, 4, 0, 3, 5, 3, 0, 3],
    [4, 4, 1]]
  commCodes := [[], [], []]
  starts := [436207996164044330534392384805412275113070828381794749284550308894716442346]
  tree := include_str "ThCover3.tree"

end CFSG.SectionRank.Native
