module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi24Sylow7Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m2"
  nregs := 69
  prog := [
      .pow 2 1 2, .mul 0 1 3, .mul 3 0 4, .mul 4 1 5, .mul 5 0 6,
      .mul 6 1 7, .mul 7 0 8, .mul 8 1 9, .mul 9 0 10, .mul 10 2 11,
      .mul 11 0 12, .mul 12 2 13, .mul 13 0 14, .mul 14 2 15, .mul 15 0 16,
      .mul 16 1 17, .mul 17 0 18, .mul 18 1 19, .mul 19 0 20, .mul 20 1 21,
      .mul 21 0 22, .mul 22 1 23, .pow 3 23 24, .mul 1 0 25, .mul 25 1 26,
      .mul 26 0 27, .mul 27 2 28, .mul 28 0 29, .mul 29 2 30, .mul 30 0 31,
      .mul 31 2 32, .mul 27 1 33, .mul 33 0 34, .mul 34 2 35, .mul 35 0 36,
      .mul 36 2 37, .mul 32 0 38, .mul 38 37 39, .pow 4 24 40, .mul 39 24 41,
      .mul 41 39 42, .mul 42 24 43, .mul 43 39 44, .mul 44 24 45, .mul 45 39 46,
      .mul 46 40 47, .pow 3 47 48, .mul 39 48 49, .mul 49 48 50, .mul 49 50 51,
      .mul 50 50 52, .mul 52 52 53, .mul 52 53 54, .pow 7 49 55, .pow 16 55 56,
      .mul 56 54 57, .mul 57 55 58, .pow 5 51 59, .pow 2 59 60, .mul 60 52 61,
      .mul 61 59 62, .pow 5 62 63, .mul 58 62 64, .pow 3 64 65, .mul 58 63 66,
      .pow 3 66 67]
  rx := 65
  ry := 67
  rh := 68
  r := 7
  oh := 1
  a := 1
  b := 0
  c := 0
  d := 1
  k := 0
  l := 0
  μ := 1
  t := 0

end CFSG.SectionRank.Native
