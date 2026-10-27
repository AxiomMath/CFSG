module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def j4Sylow3Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J4G1-f2r112B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J4G1-f2r112B0.m2"
  nregs := 33
  prog := [
      .mul 0 1 2, .pow 3 2 3, .mul 3 1 4, .mul 1 0 5, .pow 4 4 6, .pow 16 2 7, .pow 36 7 8,
      .pow 24 5 9, .mul 8 9 10, .pow 32 10 11, .mul 11 6 12, .mul 12 10 13, .pow 8 5 14,
      .mul 2 14 15, .pow 18 2 16, .mul 15 16 17, .pow 22 17 18, .mul 18 0 19, .mul 19 17 20,
      .pow 1 20 21, .mul 21 13 22, .mul 22 20 23, .pow 5 13 24, .mul 23 24 25, .mul 20 24 26,
      .mul 26 21 27, .mul 27 24 28, .mul 28 24 29, .mul 29 24 30, .mul 30 21 31, .mul 31 13 32]
  rx := 25
  ry := 32
  rh := 21
  r := 3
  oh := 2
  a := 2
  b := 0
  c := 0
  d := 2
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def j4Sylow11Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J4G1-f2r112B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J4G1-f2r112B0.m2"
  nregs := 31
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 3 6, .pow 4 3 7, .pow 8 6 8,
      .pow 32 8 9, .mul 9 7 10, .mul 10 8 11, .mul 0 11 12, .mul 12 11 13, .pow 3 13 14,
      .mul 12 12 15, .mul 14 15 16, .pow 6 12 17, .mul 17 16 18, .mul 0 18 19, .mul 19 0 20,
      .pow 39 18 21, .mul 20 21 22, .mul 21 21 23, .mul 23 21 24, .mul 24 0 25, .mul 25 18 26,
      .pow 1 0 27, .mul 26 27 28, .mul 28 18 29, .mul 29 18 30]
  rx := 22
  ry := 30
  rh := 27
  r := 11
  oh := 2
  a := 10
  b := 0
  c := 0
  d := 10
  k := 0
  l := 5
  μ := 1
  t := 0

end CFSG.SectionRank.Native
