module

public import Certificates.Data.KFCub2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def thFiveData : Cub2Data where
  seedA := include_str "../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  nregs := 21
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 5, .mul 5 3 4, .pow 4 2 7, .pow 1 7 5, .mul 5 4 1, 
      .pow 10 1 8, .pow 1 8 0, .mul 5 3 4, .pow 5 4 9, .pow 1 9 1, .pow 7 2 10, .pow 1 10 6, .mul 5 5 2, 
      .pow 5 3 11, .pow 1 11 4, .mul 4 6 5, .mul 2 5 4, .pow 17 4 12, .pow 1 12 5, .mul 5 0 6, .mul 6 4 0, 
      .mul 2 2 6, .pow 11 3 13, .pow 1 13 5, .mul 6 5 4, .pow 35 4 14, .pow 1 14 5, .mul 5 1 6, .mul 6 4 1, 
      .pow 2 0 15, .pow 3 1 16, .pow 1 0 17, .mul 17 1 17, .mul 17 1 17, .mul 17 0 17, .mul 17 1 17, .mul 17 0 17, 
      .mul 17 16 17, .mul 17 15 17, .mul 17 16 17, .mul 17 16 17, .pow 1 16 18, .mul 18 15 18, .mul 18 16 18, .mul 18 0 18, 
      .mul 18 16 18, .mul 18 15 18, .mul 18 16 18, .mul 18 15 18, .mul 18 16 18, .mul 18 0 18, .mul 18 16 18, .mul 18 15 18, 
      .mul 18 16 18, .mul 18 0 18, .mul 18 1 18, .mul 18 15 18, .mul 18 16 18, .mul 18 16 18, .mul 18 15 18, .pow 1 0 19, 
      .pow 1 1 20]
  rx := 17
  ry := 18
  r := 5
  t := 0
  h1 := { rh := 19, oh := 3, a := 2, b := 4, k := 2, c := 2, d := 2, l := 0 }
  h2 := { rh := 20, oh := 4, a := 0, b := 1, k := 3, c := 3, d := 2, l := 4 }

end CFSG.SectionRank.Native
