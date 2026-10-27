module

public import Certificates.Data.KFCub2
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def mclFiveData : Cub2Data where
  seedA := include_str "../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 15
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 1 5, .mul 5 3 1, .mul 3 3 6, .mul 6 6 0, .mul 4 4 5, 
      .mul 5 5 4, .pow 6 4 7, .pow 1 7 5, .mul 5 0 6, .mul 6 4 0, .mul 3 2 4, .mul 4 4 3, .mul 3 3 4, 
      .pow 6 4 8, .pow 1 8 5, .mul 5 1 6, .mul 6 4 1, .pow 2 0 9, .pow 7 1 10, .pow 1 10 11, .mul 11 0 11, 
      .mul 11 10 11, .mul 11 10 11, .mul 11 10 11, .mul 11 10 11, .mul 11 9 11, .mul 11 9 11, .mul 11 10 11, .mul 11 0 11, 
      .mul 11 10 11, .mul 11 9 11, .mul 11 10 11, .pow 1 1 12, .mul 12 1 12, .mul 12 1 12, .mul 12 9 12, .mul 12 10 12, 
      .mul 12 0 12, .mul 12 10 12, .mul 12 10 12, .mul 12 10 12, .mul 12 9 12, .mul 12 10 12, .mul 12 10 12, .mul 12 10 12, 
      .mul 12 9 12, .mul 12 10 12, .mul 12 10 12, .mul 12 9 12, .mul 12 9 12, .mul 12 10 12, .mul 12 10 12, .pow 1 0 13, 
      .pow 1 1 14]
  rx := 11
  ry := 12
  r := 5
  t := 0
  h1 := { rh := 13, oh := 3, a := 4, b := 4, k := 1, c := 1, d := 0, l := 0 }
  h2 := { rh := 14, oh := 8, a := 3, b := 4, k := 3, c := 1, d := 2, l := 1 }

end CFSG.SectionRank.Native
