module

public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3

public section

namespace CFSG.SectionRank.Native

@[expose] def lyMax7Cover3 : Cover3Data (Array Nat) where
  seedA := include_str "../../../../CFSG/Blueprint/Data/LyG1-f5r111B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/LyG1-f5r111B0.m2"
  m := 3
  nregs := 9
  prog := [.mul 0 1 2, .mul 2 1 3, .mul 3 1 4, .mul 4 1 5, .mul 5 4 5, .mul 5 2 5, 
      .pow 4 3 3, .mul 3 5 3, .mul 2 3 2, .pow 12 2 3, .pow 4 1 5, .mul 3 5 5, 
      .mul 3 1 4, .mul 5 4 5, .pow 3 5 5, .mul 0 5 4, .mul 3 2 3, .mul 2 5 6, 
      .mul 2 6 6, .mul 4 6 4, .mul 2 6 6, .mul 4 6 4, .mul 4 5 4, .mul 6 6 6, 
      .mul 4 6 4, .pow 5 2 2, .mul 4 2 4, .mul 4 6 4, .pow 23 3 6, .pow 11 4 2, 
      .mul 2 6 5, .mul 5 2 5, .mul 5 3 5, .mul 5 3 5, .mul 5 6 5, .mul 5 2 5, 
      .mul 5 3 5, .mul 5 6 5, .mul 5 4 5, .mul 5 2 5, .mul 5 4 5, .mul 5 6 5, 
      .mul 5 4 5, .mul 5 3 5, .mul 5 4 5, .mul 5 6 5, .mul 5 6 5, .mul 5 4 5, 
      .mul 5 2 5, .mul 5 3 5, .mul 5 2 5, .mul 5 4 5, .mul 5 2 5, .mul 5 6 5, 
      .mul 5 3 5, .mul 5 6 5, .mul 5 2 5, .mul 5 3 5, .mul 5 6 5, .mul 5 2 5, 
      .mul 5 3 5, .mul 5 4 5, .mul 5 2 5, .mul 5 4 5, .mul 5 6 5, .mul 5 4 5, 
      .mul 5 2 5, .mul 5 4 5, .mul 5 3 5, .mul 5 3 5, .mul 5 4 5, .mul 5 6 5, 
      .mul 5 2 5, .mul 5 3 5, .mul 5 4 5, .mul 5 3 5, .mul 5 2 5, .mul 5 2 5, 
      .mul 4 6 7, .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7, .mul 7 2 7, 
      .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 6 7, .mul 7 4 7, .mul 7 3 7, 
      .mul 7 4 7, .mul 7 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 4 7, .mul 7 6 7, 
      .mul 7 4 7, .mul 7 2 7, .mul 7 2 7, .mul 7 4 7, .mul 7 6 7, .mul 7 6 7, 
      .mul 7 2 7, .mul 7 3 7, .mul 7 6 7, .mul 7 4 7, .mul 7 4 7, .mul 7 2 7, 
      .mul 7 6 7, .mul 7 3 7, .mul 7 6 7, .mul 7 3 7, .mul 7 6 7, .mul 7 2 7, 
      .mul 7 3 7, .mul 7 6 7, .mul 7 4 7, .mul 7 4 7, .mul 7 2 7, .mul 7 6 7, 
      .mul 7 3 7, .mul 7 3 7, .mul 7 4 7, .mul 7 3 7, .mul 7 4 7, .mul 7 2 7, 
      .mul 7 3 7, .mul 7 3 7, .mul 3 6 8, .mul 8 4 8, .mul 8 3 8, .mul 8 4 8, 
      .mul 8 4 8, .mul 8 6 8, .mul 8 3 8, .mul 8 3 8, .mul 8 6 8, .mul 8 2 8, 
      .mul 8 6 8, .mul 8 3 8, .mul 8 4 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, 
      .mul 8 3 8, .mul 8 2 8, .mul 8 4 8, .mul 8 4 8, .mul 8 4 8, .mul 8 3 8, 
      .mul 8 2 8, .mul 8 3 8, .mul 8 6 8, .mul 8 4 8, .mul 8 2 8, .mul 8 2 8, 
      .mul 8 6 8, .mul 8 4 8, .mul 8 4 8, .mul 8 4 8, .mul 8 6 8, .mul 8 3 8, 
      .mul 8 4 8, .mul 8 6 8, .mul 8 3 8, .mul 8 6 8, .mul 8 4 8, .mul 8 3 8, 
      .mul 8 4 8, .mul 8 4 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 6 8, 
      .mul 8 6 8, .mul 8 2 8]
  regs := [5, 7, 8]
  ordv := [8, 4, 8]
  ord := [8, 4, 8]
  relCodes := [[0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4],
    [2, 2, 5, 0, 2, 2, 4, 2, 4, 3, 1, 2, 5, 2],
    [2, 2, 0, 5, 0, 4, 3, 5, 3, 4, 3, 4, 2, 4],
    [0, 3, 5, 3, 5, 5, 0, 2, 5, 2, 5, 5, 3, 3],
    [2, 0, 4, 4, 4, 3, 0, 3, 0, 4, 4, 4, 2, 0],
    [4, 4, 4, 2, 2, 4, 0, 0, 0, 3, 3, 0],
    [2, 4, 4, 2, 1, 3, 5, 3, 1, 3, 4, 2],
    [4, 1, 2, 2, 2, 0, 5, 0, 5, 2, 4, 1],
    [5, 5, 2, 0, 3, 5, 0, 3, 1, 2, 5, 1],
    [2, 1, 3, 5, 3, 3, 5, 3, 4, 4, 0, 2],
    [3, 3, 0, 4, 0, 4, 0, 5, 5, 0, 3, 3],
    [4, 3, 5, 5, 2, 5, 0, 3, 5, 2, 1, 1],
    [2, 5, 3, 5, 0, 3, 3, 4, 2, 4, 3, 1],
    [4, 4, 0, 4, 4, 4, 0, 4],
    [0, 0, 4, 0, 4, 0, 5, 5],
    [4, 0, 4, 0, 4, 4, 1, 1],
    [4, 0, 4, 0, 4, 0, 5, 1],
    [3, 3, 3, 5, 0, 5, 0, 3]]
  commCodes := [[], [], []]
  starts := [#[2, 0, 2, 3, 1, 4, 1, 3, 1, 0, 4, 4, 0, 0, 3, 3, 4, 0, 4, 4, 3, 3, 2, 3, 1, 3, 0, 0, 4, 1, 4, 0, 0, 0, 0, 3, 4, 2, 3, 0, 2, 0, 3, 2, 3, 4, 0, 3, 0, 4, 3, 3, 1, 3, 0, 4, 2, 3, 1, 0, 4, 4, 3, 3, 4, 2, 1, 1, 0, 2, 1, 4, 2, 2, 2, 0, 2, 3, 3, 4, 3, 2, 3, 2, 2, 2, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2, 1, 3, 4, 0, 0, 3, 2, 4, 2, 4, 0, 4, 0, 4, 3]]
  tree := include_str "LyCover3.tree"

end CFSG.SectionRank.Native
