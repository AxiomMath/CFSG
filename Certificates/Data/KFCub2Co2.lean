module

public import Certificates.Data.KFCub2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co2FiveData : Cub2Data where
  seedA := include_str "../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
  nregs := 17
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 1 4, .mul 4 1 5, .pow 3 3 6, .pow 1 6 0, .mul 4 4 3, .mul 2 2 4, 
      .mul 4 3 1, .pow 5 1 7, .pow 1 7 3, .pow 20 5 8, .pow 1 8 4, .pow 6 2 9, .pow 1 9 5, .mul 4 5 2, 
      .pow 7 2 10, .pow 1 10 4, .mul 4 3 5, .mul 5 2 1, .pow 2 0 11, .pow 3 1 12, .pow 1 11 13, .mul 13 12 13, 
      .mul 13 12 13, .mul 13 11 13, .mul 13 12 13, .mul 13 12 13, .mul 13 11 13, .mul 13 11 13, .mul 13 12 13, .mul 13 11 13, 
      .mul 13 1 13, .pow 1 0 14, .mul 14 1 14, .mul 14 1 14, .mul 14 11 14, .mul 14 1 14, .mul 14 11 14, .mul 14 1 14, 
      .mul 14 0 14, .mul 14 0 14, .mul 14 1 14, .mul 14 11 14, .mul 14 12 14, .mul 14 11 14, .pow 1 0 15, .pow 1 1 16]
  rx := 13
  ry := 14
  r := 5
  t := 0
  h1 := { rh := 15, oh := 3, a := 2, b := 1, k := 0, c := 3, d := 2, l := 2 }
  h2 := { rh := 16, oh := 4, a := 2, b := 0, k := 0, c := 3, d := 4, l := 1 }

end CFSG.SectionRank.Native
