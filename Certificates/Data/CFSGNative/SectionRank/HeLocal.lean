module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def heSylow3Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m2"
  nregs := 40
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 1 4, .pow 3 1 5, .mul 4 5 6, .mul 5 3 7, .mul 7 6 8,
      .mul 8 4 9, .mul 0 9 10, .pow 1 0 11, .mul 10 11 12, .mul 12 11 13, .mul 13 11 14,
      .pow 6 9 15, .mul 14 15 16, .mul 16 0 17, .mul 17 9 18, .mul 9 9 19, .mul 19 9 20,
      .mul 20 11 21, .mul 21 9 22, .mul 22 9 23, .mul 23 9 24, .mul 0 15 25, .mul 25 15 26,
      .mul 26 0 27, .mul 27 15 28, .mul 28 15 29, .mul 29 15 30, .mul 30 11 31, .mul 31 9 32,
      .mul 32 9 33, .mul 33 9 34, .mul 34 0 35, .mul 35 15 36, .mul 36 15 37, .pow 4 18 38,
      .pow 4 24 39]
  rx := 38
  ry := 39
  rh := 37
  r := 3
  oh := 12
  a := 0
  b := 2
  c := 1
  d := 0
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def heSylow5Data : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m2"
  nregs := 27
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 3 1 5, .mul 5 1 6, .mul 4 6 7, .mul 7 2 8,
      .pow 11 8 9, .mul 9 9 10, .mul 10 9 11, .mul 11 0 12, .mul 12 9 13, .mul 13 9 14,
      .mul 14 9 15, .pow 1 0 16, .mul 15 16 17, .mul 17 16 18, .mul 8 8 19, .mul 19 0 20,
      .mul 20 8 21, .mul 21 8 22, .mul 22 8 23, .mul 23 8 24, .pow 2 18 25, .pow 2 24 26]
  rx := 25
  ry := 26
  rh := 8
  r := 5
  oh := 12
  a := 2
  b := 4
  c := 4
  d := 0
  t := 0

@[expose] def heSylow7Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m2"
  nregs := 25
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 3 3 5, .mul 5 5 6, .mul 5 6 7, .pow 7 2 8,
      .pow 16 8 9, .mul 9 7 10, .mul 10 8 11, .pow 5 4 12, .pow 2 12 13, .mul 13 5 14,
      .mul 14 12 15, .pow 1 11 16, .pow 5 15 17, .mul 16 17 18, .mul 11 15 19, .mul 17 16 20,
      .mul 20 16 21, .mul 21 16 22, .pow 3 18 23, .pow 3 19 24]
  rx := 23
  ry := 24
  rh := 22
  r := 7
  oh := 21
  a := 2
  b := 0
  c := 0
  d := 1
  k := 3
  l := 0
  μ := 2
  t := 0

end CFSG.SectionRank.Native
