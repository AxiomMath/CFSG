module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def ruSylow3Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m2"
  nregs := 39
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 3 4 5, .mul 5 4 6, .mul 6 6 7, .mul 5 7 8,
      .mul 4 8 9, .mul 5 5 10, .mul 10 10 11, .mul 11 9 12, .mul 12 12 13, .mul 2 4 14,
      .mul 14 4 15, .pow 9 15 16, .mul 14 16 17, .pow 14 17 18, .mul 18 13 19, .mul 19 17 20,
      .pow 3 20 21, .pow 1 0 22, .mul 21 22 23, .mul 23 21 24, .mul 24 22 25, .mul 25 21 26,
      .mul 20 20 27, .mul 27 0 28, .mul 28 21 29, .mul 29 22 30, .mul 30 21 31, .mul 31 0 32,
      .mul 32 20 33, .mul 33 22 34, .mul 0 21 35, .mul 35 21 36, .pow 2 26 37, .pow 2 34 38]
  rx := 37
  ry := 38
  rh := 36
  r := 3
  oh := 8
  a := 2
  b := 1
  c := 2
  d := 2
  k := 1
  l := 1
  μ := 2
  t := 0

@[expose] def ruSylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m2"
  nregs := 37
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 3 4 5, .mul 5 4 6, .mul 6 6 7, .mul 5 7 8,
      .mul 4 8 9, .mul 5 5 10, .mul 10 10 11, .mul 11 9 12, .mul 12 12 13, .mul 2 4 14,
      .pow 6 14 15, .mul 14 4 16, .pow 10 16 17, .mul 15 17 18, .pow 25 18 19, .mul 19 13 20,
      .mul 20 18 21, .pow 3 21 22, .pow 1 0 23, .mul 22 23 24, .mul 24 22 25, .mul 25 23 26,
      .mul 26 22 27, .mul 0 21 28, .mul 28 21 29, .mul 29 23 30, .mul 30 22 31, .mul 23 21 32,
      .mul 32 0 33, .mul 33 21 34, .pow 4 27 35, .pow 4 31 36]
  rx := 35
  ry := 36
  rh := 34
  r := 5
  oh := 4
  a := 3
  b := 0
  c := 0
  d := 3
  k := 3
  l := 4
  μ := 4
  t := 0

end CFSG.SectionRank.Native
