module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def j2Sylow3Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J2G1-f5r14B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J2G1-f5r14B0.m2"
  nregs := 26
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 4 4 6, .mul 6 2 7, .pow 3 5 8,
      .pow 5 7 9, .mul 9 8 10, .mul 10 7 11, .pow 3 11 12, .pow 1 0 13, .mul 12 13 14,
      .mul 14 11 15, .mul 15 13 16, .mul 16 12 17, .mul 0 11 18, .mul 18 13 19, .mul 19 11 20,
      .mul 20 13 21, .mul 21 11 22, .mul 22 13 23, .mul 11 11 24, .mul 24 0 25]
  rx := 17
  ry := 23
  rh := 25
  r := 3
  oh := 8
  a := 2
  b := 1
  c := 1
  d := 0
  k := 2
  l := 0
  μ := 2
  t := 0

@[expose] def j2Sylow5Data : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J2G1-f5r14B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J2G1-f5r14B0.m2"
  nregs := 26
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8,
      .mul 8 3 9, .pow 6 4 10, .mul 4 4 11, .mul 11 2 12, .mul 12 2 13, .mul 2 9 14, .mul 3 4 15,
      .mul 14 15 16, .pow 11 13 17, .mul 17 16 18, .mul 18 13 19, .pow 1 10 20, .mul 19 20 21,
      .pow 5 19 22, .mul 22 10 23, .pow 2 21 24, .pow 2 23 25]
  rx := 24
  ry := 25
  rh := 10
  r := 5
  oh := 2
  a := 0
  b := 4
  c := 4
  d := 0
  t := 0

end CFSG.SectionRank.Native
