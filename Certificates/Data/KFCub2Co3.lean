module

public import Certificates.Data.KFCub2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co3FiveData : Cub2Data where
  seedA := include_str "../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
  nregs := 18
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .pow 3 2 9, .pow 1 9 5, .pow 9 4 10, .pow 1 10 6, .mul 5 6 7, 
      .pow 29 7 11, .pow 1 11 8, .mul 8 1 5, .mul 5 7 1, .pow 2 0 12, .pow 3 1 13, .pow 1 0 14, .mul 14 1 14, 
      .mul 14 0 14, .mul 14 1 14, .mul 14 1 14, .mul 14 12 14, .mul 14 1 14, .mul 14 12 14, .mul 14 1 14, .mul 14 0 14, 
      .mul 14 13 14, .mul 14 13 14, .mul 14 12 14, .mul 14 13 14, .mul 14 12 14, .mul 14 1 14, .mul 14 0 14, .mul 14 1 14, 
      .mul 14 1 14, .mul 14 12 14, .mul 14 13 14, .mul 14 0 14, .mul 14 1 14, .mul 14 1 14, .pow 1 13 15, .mul 15 13 15, 
      .mul 15 12 15, .mul 15 1 15, .mul 15 0 15, .mul 15 13 15, .mul 15 13 15, .mul 15 12 15, .mul 15 13 15, .mul 15 13 15, 
      .mul 15 12 15, .mul 15 13 15, .mul 15 0 15, .mul 15 13 15, .mul 15 0 15, .mul 15 1 15, .mul 15 12 15, .mul 15 13 15, 
      .mul 15 0 15, .mul 15 13 15, .mul 15 0 15, .mul 15 1 15, .mul 15 12 15, .mul 15 13 15, .mul 15 0 15, .mul 15 1 15, 
      .mul 15 0 15, .mul 15 13 15, .pow 1 12 16, .mul 16 1 16, .mul 16 0 16, .mul 16 1 16, .mul 16 1 16, .mul 16 12 16, 
      .mul 16 13 16, .mul 16 0 16, .mul 16 1 16, .mul 16 1 16, .mul 16 12 16, .mul 16 13 16, .mul 16 12 16, .mul 16 13 16, 
      .mul 16 13 16, .mul 16 12 16, .mul 16 13 16, .mul 16 12 16, .mul 16 12 16, .mul 16 1 16, .mul 16 1 16, .mul 16 12 16, 
      .mul 16 1 16, .mul 16 12 16, .mul 16 1 16, .pow 1 12 17, .mul 17 1 17, .mul 17 0 17, .mul 17 1 17, .mul 17 1 17, 
      .mul 17 12 17, .mul 17 13 17, .mul 17 0 17, .mul 17 1 17, .mul 17 1 17, .mul 17 12 17, .mul 17 13 17, .mul 17 12 17, 
      .mul 17 13 17, .mul 17 13 17, .mul 17 12 17, .mul 17 13 17, .mul 17 12 17, .mul 17 12 17, .mul 17 1 17, .mul 17 1 17, 
      .mul 17 12 17, .mul 17 1 17, .mul 17 12 17, .mul 17 1 17]
  rx := 14
  ry := 15
  r := 5
  t := 0
  h1 := { rh := 16, oh := 24, a := 3, b := 3, k := 1, c := 2, d := 1, l := 1 }
  h2 := { rh := 17, oh := 24, a := 3, b := 3, k := 1, c := 2, d := 1, l := 1 }

end CFSG.SectionRank.Native
