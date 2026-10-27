module

public import Certificates.Data.CFSGNative.SectionRank.LocalDet
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def j3LocDetData : LocDetData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J3G1-f2r80B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J3G1-f2r80B0.m2"
  nregs := 98
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 3 4, .pow 18 4 5, .mul 5 1 6, .mul 6 4 7, .pow 18 2 8,
      .mul 8 0 9, .mul 9 2 10, .mul 7 10 11, .mul 11 7 12, .mul 12 7 13, .mul 13 10 14,
      .mul 14 7 15, .mul 10 7 16, .mul 16 10 17, .mul 17 7 18, .mul 12 10 19, .mul 19 7 20,
      .mul 20 10 21, .mul 21 7 22, .mul 22 7 23, .mul 23 10 24, .mul 24 7 25, .mul 25 10 26,
      .mul 26 7 27, .mul 27 7 28, .mul 28 10 29, .mul 29 7 30, .mul 30 10 31, .mul 31 7 32,
      .mul 32 7 33, .mul 33 10 34, .mul 7 7 35, .mul 35 10 36, .mul 36 7 37, .mul 37 10 38,
      .mul 38 7 39, .mul 39 10 40, .mul 40 7 41, .mul 41 10 42, .mul 42 7 43, .mul 43 7 44,
      .mul 44 10 45, .mul 45 7 46, .mul 46 10 47, .mul 47 7 48, .mul 48 7 49, .mul 49 10 50,
      .mul 50 7 51, .mul 51 10 52, .mul 18 7 53, .mul 53 10 54, .mul 54 7 55, .mul 55 10 56,
      .mul 56 7 57, .mul 57 7 58, .mul 58 10 59, .mul 59 7 60, .mul 60 10 61, .mul 61 7 62,
      .mul 62 7 63, .mul 63 10 64, .mul 64 7 65, .mul 65 10 66, .mul 66 7 67, .mul 67 7 68,
      .mul 68 10 69, .mul 69 7 70, .mul 70 10 71, .mul 71 7 72, .mul 72 7 73, .mul 16 7 74,
      .mul 74 10 75, .mul 75 7 76, .mul 76 7 77, .mul 77 10 78, .mul 78 7 79, .mul 79 10 80,
      .mul 80 7 81, .mul 81 10 82, .mul 82 7 83, .mul 83 7 84, .mul 84 10 85, .mul 85 7 86,
      .mul 86 7 87, .mul 15 7 88, .mul 88 10 89, .mul 89 7 90, .mul 90 10 91, .mul 91 7 92,
      .mul 92 10 93, .mul 93 7 94, .mul 94 7 95, .mul 95 10 96, .mul 96 7 97]
  rk1 := 15
  rk2 := 18
  ok1 := 4
  ok2 := 4
  nK := 360
  rx := 34
  ry := 52
  rh := 16
  oh := 8
  a := 2
  b := 1
  c := 1
  d := 0
  rc := 73
  ru1 := 18
  rv1 := 87
  ru2 := 97
  rv2 := 19
  t := 0

end CFSG.SectionRank.Native
