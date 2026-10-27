module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def hsSylow3Data : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m2"
  nregs := 38
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8,
      .mul 8 3 9, .mul 9 9 10, .mul 9 10 11, .mul 2 2 12, .mul 2 12 13, .mul 13 13 14,
      .pow 10 14 15, .mul 15 11 16, .mul 16 14 17, .mul 3 3 18, .mul 3 18 19, .pow 9 19 20,
      .mul 19 5 21, .mul 21 20 22, .pow 6 22 23, .mul 23 23 24, .mul 24 17 25, .pow 1 17 26,
      .mul 22 26 27, .mul 27 23 28, .mul 28 23 29, .mul 29 23 30, .mul 30 17 31, .mul 31 23 32,
      .mul 32 23 33, .mul 17 22 34, .mul 34 22 35, .pow 2 25 36, .pow 2 33 37]
  rx := 36
  ry := 37
  rh := 35
  r := 3
  oh := 6
  a := 1
  b := 2
  c := 0
  d := 2
  t := 0

@[expose] def hsSylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m2"
  nregs := 59
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8,
      .mul 8 3 9, .mul 9 9 10, .mul 9 10 11, .mul 6 8 12, .mul 2 2 13, .mul 13 13 14, .pow 10 14 15,
      .mul 14 12 16, .mul 16 15 17, .pow 5 4 18, .pow 2 18 19, .mul 18 11 20, .mul 20 19 21,
      .pow 1 21 22, .mul 22 17 23, .mul 23 22 24, .pow 3 17 25, .mul 24 25 26, .mul 26 22 27,
      .mul 27 25 28, .mul 28 25 29, .mul 29 22 30, .mul 30 25 31, .mul 31 21 32, .mul 32 17 33,
      .mul 33 22 34, .mul 34 25 35, .mul 35 25 36, .mul 36 22 37, .mul 21 17 38, .mul 38 21 39,
      .mul 39 17 40, .mul 40 21 41, .mul 41 25 42, .mul 42 21 43, .mul 43 17 44, .mul 44 21 45,
      .mul 45 17 46, .mul 46 17 47, .mul 47 21 48, .mul 48 17 49, .mul 49 21 50, .mul 50 21 51,
      .mul 51 17 52, .mul 52 21 53, .mul 53 17 54, .mul 54 17 55, .mul 55 17 56, .pow 2 37 57,
      .pow 2 56 58]
  rx := 57
  ry := 58
  rh := 17
  r := 5
  oh := 4
  a := 3
  b := 0
  c := 0
  d := 3
  k := 0
  l := 0
  μ := 4
  t := 0

end CFSG.SectionRank.Native
