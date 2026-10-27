module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def mclMultData : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 29
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 1 5, .mul 5 3 6, .mul 3 3 7, .mul 7 7 8,
      .mul 4 4 9, .mul 9 9 10, .pow 6 10 11, .mul 11 8 12, .mul 12 10 13, .mul 3 2 14,
      .mul 14 14 15, .mul 15 15 16, .pow 6 16 17, .mul 17 6 18, .mul 18 16 19, .pow 1 19 20,
      .mul 20 13 20, .pow 3 19 21, .mul 20 21 20, .pow 2 13 22, .mul 20 22 20, .mul 20 19 20,
      .mul 20 13 20, .pow 3 19 23, .mul 20 23 20, .pow 1 19 24, .mul 24 19 24, .mul 24 13 24,
      .pow 4 19 25, .mul 24 25 24, .pow 2 13 26, .mul 24 26 24, .pow 2 19 27, .mul 24 27 24,
      .pow 1 13 28]
  rx := 20
  ry := 24
  rh := 28
  r := 5
  oh := 3
  a := 1
  b := 2
  c := 1
  d := 3
  k := 3
  l := 0
  μ := 1
  t := 0

@[expose] def co2MultData : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
  nregs := 25
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 1 4, .mul 4 1 5, .pow 3 3 6, .mul 4 4 7, .mul 2 2 8,
      .mul 8 7 9, .pow 5 9 10, .pow 20 5 11, .pow 6 2 12, .mul 11 12 13, .pow 7 13 14,
      .mul 14 10 15, .mul 15 13 16, .pow 1 6 17, .mul 17 6 17, .mul 17 16 17, .mul 17 6 17,
      .pow 2 16 18, .mul 17 18 17, .mul 17 6 17, .mul 17 16 17, .mul 17 6 17, .mul 17 16 17,
      .mul 17 6 17, .pow 2 16 19, .mul 17 19 17, .mul 17 6 17, .mul 17 16 17, .mul 17 6 17,
      .pow 1 6 20, .mul 20 6 20, .mul 20 16 20, .mul 20 6 20, .mul 20 16 20, .mul 20 6 20,
      .pow 3 16 21, .mul 20 21 20, .pow 2 6 22, .mul 20 22 20, .pow 3 16 23, .mul 20 23 20,
      .pow 1 6 24]
  rx := 17
  ry := 20
  rh := 24
  r := 5
  oh := 3
  a := 3
  b := 3
  c := 4
  d := 1
  k := 3
  l := 2
  μ := 1
  t := 0

@[expose] def thMultData5 : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  nregs := 31
  prog := [
      .mul 0 1 2, .mul 2 1 3, .pow 5 2 4, .mul 4 1 5, .pow 5 5 6, .pow 3 2 7, .pow 15 3 8,
      .mul 7 8 9, .pow 17 9 10, .mul 10 0 11, .mul 11 9 12, .pow 8 3 13, .pow 9 2 14,
      .mul 13 14 15, .pow 19 15 16, .mul 16 6 17, .mul 17 15 18, .pow 1 12 19, .pow 2 18 20,
      .mul 19 20 19, .mul 19 12 19, .mul 19 18 19, .mul 19 12 19, .pow 2 18 21, .mul 19 21 19,
      .mul 19 12 19, .pow 2 18 22, .mul 19 22 19, .mul 19 12 19, .pow 3 18 23, .mul 19 23 19,
      .mul 19 12 19, .pow 2 18 24, .mul 19 24 19, .pow 1 12 25, .mul 25 18 25, .mul 25 12 25,
      .pow 3 18 26, .mul 25 26 25, .mul 25 12 25, .pow 2 18 27, .mul 25 27 25, .pow 1 12 28,
      .pow 2 18 29, .mul 28 29 28, .mul 28 12 28, .pow 2 18 30, .mul 28 30 28, .mul 28 12 28]
  rx := 19
  ry := 25
  rh := 28
  r := 5
  oh := 2
  a := 4
  b := 0
  c := 0
  d := 4
  k := 4
  l := 3
  μ := 1
  t := 0

@[expose] def thMultData7 : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  nregs := 29
  prog := [
      .mul 0 1 2, .mul 2 1 3, .pow 4 2 4, .mul 4 3 5, .pow 8 3 6, .mul 6 3 7, .mul 2 2 8,
      .mul 6 8 9, .pow 5 2 10, .mul 10 10 11, .mul 10 9 12, .mul 11 7 13, .pow 5 5 14,
      .pow 17 12 15, .mul 1 12 16, .mul 15 16 17, .pow 3 13 18, .mul 14 13 19, .mul 18 19 20,
      .pow 1 20 21, .pow 2 17 22, .mul 21 22 21, .pow 2 20 23, .mul 21 23 21, .mul 21 17 21,
      .mul 21 20 21, .pow 1 17 24, .mul 24 20 24, .pow 2 17 25, .mul 24 25 24, .pow 2 20 26,
      .mul 24 26 24, .mul 24 17 24, .mul 24 20 24, .pow 2 17 27, .mul 24 27 24, .pow 1 17 28]
  rx := 21
  ry := 24
  rh := 28
  r := 7
  oh := 3
  a := 0
  b := 3
  c := 1
  d := 5
  t := 0

@[expose] def suzMultData : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/SuzG1-f3r64B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/SuzG1-f3r64B0.m2"
  nregs := 34
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8,
      .mul 8 3 9, .mul 4 9 10, .pow 3 10 11, .pow 12 2 12, .pow 12 12 13, .mul 13 11 14,
      .mul 14 12 15, .pow 12 4 16, .pow 3 6 17, .mul 16 17 18, .pow 9 18 19, .mul 19 11 20,
      .mul 20 18 21, .pow 1 15 22, .pow 2 15 23, .mul 22 23 22, .mul 22 21 22, .mul 22 15 22,
      .pow 3 21 24, .mul 22 24 22, .mul 22 15 22, .pow 2 21 25, .mul 22 25 22, .mul 22 15 22,
      .mul 22 21 22, .pow 3 15 26, .mul 22 26 22, .mul 22 21 22, .mul 22 15 22, .pow 1 21 27,
      .mul 27 15 27, .pow 3 21 28, .mul 27 28 27, .pow 2 15 29, .mul 27 29 27, .mul 27 21 27,
      .mul 27 15 27, .mul 27 21 27, .pow 1 21 30, .mul 30 15 30, .mul 30 21 30, .pow 2 15 31,
      .mul 30 31 30, .pow 2 21 32, .mul 30 32 30, .pow 2 15 33, .mul 30 33 30]
  rx := 22
  ry := 27
  rh := 30
  r := 5
  oh := 4
  a := 3
  b := 0
  c := 0
  d := 3
  t := 0

@[expose] def co3MultData : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
  nregs := 26
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .pow 3 2 5, .pow 9 4 6, .mul 5 6 7, .pow 29 7 8,
      .mul 8 1 9, .mul 9 7 10, .pow 1 0 11, .mul 11 0 11, .mul 11 10 11, .mul 11 0 11,
      .mul 11 10 11, .pow 2 0 12, .mul 11 12 11, .pow 3 10 13, .mul 11 13 11, .pow 2 0 14,
      .mul 11 14 11, .pow 2 10 15, .mul 11 15 11, .mul 11 0 11, .mul 11 10 11, .pow 2 0 16,
      .mul 11 16 11, .mul 11 10 11, .pow 2 0 17, .mul 11 17 11, .pow 3 10 18, .mul 11 18 11,
      .pow 1 10 19, .pow 2 10 20, .mul 19 20 19, .pow 2 0 21, .mul 19 21 19, .mul 19 10 19,
      .mul 19 0 19, .mul 19 10 19, .mul 19 0 19, .mul 19 10 19, .mul 19 0 19, .pow 3 10 22,
      .mul 19 22 19, .pow 2 0 23, .mul 19 23 19, .mul 19 10 19, .pow 1 0 24, .mul 24 10 24,
      .mul 24 0 24, .mul 24 10 24, .pow 2 0 25, .mul 24 25 24]
  rx := 11
  ry := 19
  rh := 24
  r := 5
  oh := 24
  a := 1
  b := 2
  c := 2
  d := 2
  k := 2
  l := 4
  μ := 3
  t := 0

@[expose] def onMultData : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
  nregs := 19
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 3 4, .pow 18 4 3, .mul 3 1 5, .mul 5 4 1, .pow 10 2 3,
      .mul 3 0 4, .mul 4 2 0, .pow 1 0 9, .pow 3 1 10, .pow 1 0 11, .mul 11 1 11, .mul 11 0 11,
      .mul 11 1 11, .mul 11 0 11, .mul 11 1 11, .mul 11 1 11, .pow 4 11 7, .pow 1 0 11,
      .mul 11 1 11, .mul 11 1 11, .mul 11 0 11, .mul 11 10 11, .mul 11 0 11, .mul 11 10 11,
      .pow 4 11 8, .pow 1 0 13, .pow 3 1 14, .pow 1 14 15, .mul 15 1 15, .mul 15 0 15,
      .mul 15 13 15, .pow 2 0 16, .mul 15 16 15, .pow 2 13 17, .mul 15 17 15, .mul 15 0 15,
      .mul 15 14 15, .pow 2 1 18, .mul 15 18 15, .mul 15 0 15, .mul 15 1 15, .mul 15 14 15,
      .mul 15 1 15, .mul 15 13 15, .mul 15 1 15, .mul 15 13 15, .mul 15 14 15, .mul 15 0 15,
      .mul 15 14 15, .mul 15 13 15]
  rx := 7
  ry := 8
  rh := 15
  r := 7
  oh := 4
  a := 0
  b := 6
  c := 1
  d := 0
  k := 0
  l := 4
  μ := 1
  t := 0

@[expose] def co1MultData : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co1G1-f2r24B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co1G1-f2r24B0.m2"
  nregs := 56
  prog := [
      .pow 2 1 2, .mul 0 1 3, .mul 0 2 4, .mul 1 0 5, .mul 2 0 6, .pow 1 5 7, .mul 7 1 7,
      .mul 7 5 7, .pow 2 6 8, .mul 7 8 7, .mul 7 2 7, .mul 7 0 7, .pow 2 6 9, .mul 7 9 7,
      .mul 7 4 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 2 7, .pow 3 5 10, .mul 7 10 7,
      .mul 7 6 7, .mul 7 0 7, .mul 7 4 7, .mul 7 0 7, .mul 7 4 7, .mul 7 1 7, .mul 7 5 7,
      .mul 7 1 7, .mul 7 3 7, .mul 7 2 7, .mul 7 5 7, .mul 7 2 7, .mul 7 0 7, .pow 3 2 11,
      .mul 7 11 7, .mul 7 0 7, .mul 7 4 7, .mul 7 1 7, .mul 7 6 7, .mul 7 1 7, .mul 7 6 7,
      .mul 7 5 7, .pow 3 7 12, .pow 1 6 13, .mul 13 6 13, .mul 13 5 13, .mul 13 1 13, .mul 13 3 13,
      .mul 13 2 13, .mul 13 0 13, .mul 13 1 13, .mul 13 0 13, .mul 13 6 13, .mul 13 4 13,
      .mul 13 1 13, .mul 13 0 13, .mul 13 3 13, .mul 13 1 13, .mul 13 5 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 5 13, .mul 13 3 13, .mul 13 5 13, .mul 13 0 13, .pow 2 5 14,
      .mul 13 14 13, .mul 13 2 13, .mul 13 0 13, .mul 13 5 13, .mul 13 0 13, .pow 2 3 15,
      .mul 13 15 13, .mul 13 5 13, .mul 13 3 13, .pow 3 5 16, .mul 13 16 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 3 13, .mul 13 4 13, .mul 13 1 13, .pow 1 2 17, .mul 17 5 17,
      .mul 17 6 17, .mul 17 0 17, .mul 17 2 17, .pow 3 4 18, .mul 17 18 17, .mul 17 6 17,
      .mul 17 4 17, .pow 2 6 19, .mul 17 19 17, .mul 17 0 17, .mul 17 4 17, .mul 17 0 17,
      .mul 17 1 17, .pow 2 4 20, .mul 17 20 17, .mul 17 0 17, .mul 17 4 17, .mul 17 6 17,
      .mul 17 4 17, .mul 17 0 17, .mul 17 2 17, .mul 17 4 17, .mul 17 2 17, .mul 17 6 17,
      .mul 17 0 17, .mul 17 2 17, .mul 17 5 17, .mul 17 3 17, .mul 17 0 17, .mul 17 2 17,
      .mul 17 0 17, .mul 17 1 17, .mul 17 6 17, .mul 17 2 17, .mul 17 4 17, .pow 2 3 21,
      .mul 17 21 17, .mul 17 12 22, .mul 22 13 23, .mul 12 23 24, .pow 1 0 25, .mul 25 3 25,
      .mul 25 5 25, .mul 25 3 25, .mul 25 4 25, .mul 25 1 25, .mul 25 4 25, .mul 25 3 25,
      .mul 25 5 25, .mul 25 2 25, .pow 2 6 26, .mul 25 26 25, .mul 25 5 25, .mul 25 3 25,
      .pow 2 4 27, .mul 25 27 25, .pow 2 6 28, .mul 25 28 25, .mul 25 1 25, .pow 3 5 29,
      .mul 25 29 25, .mul 25 2 25, .mul 25 5 25, .mul 25 1 25, .mul 25 0 25, .mul 25 5 25,
      .mul 25 1 25, .mul 25 3 25, .mul 25 5 25, .mul 25 6 25, .mul 25 5 25, .mul 25 2 25,
      .mul 25 3 25, .mul 25 0 25, .pow 2 6 30, .mul 25 30 25, .mul 25 5 25, .pow 2 2 31,
      .mul 25 31 25, .pow 1 1 32, .mul 32 1 32, .mul 32 4 32, .pow 2 3 33, .mul 32 33 32,
      .mul 32 0 32, .mul 32 6 32, .mul 32 1 32, .mul 32 4 32, .mul 32 3 32, .mul 32 4 32,
      .mul 32 6 32, .mul 32 2 32, .mul 32 4 32, .mul 32 0 32, .mul 32 2 32, .mul 32 4 32,
      .mul 32 1 32, .pow 3 4 34, .mul 32 34 32, .mul 32 2 32, .pow 2 3 35, .mul 32 35 32,
      .pow 2 5 36, .mul 32 36 32, .mul 32 6 32, .mul 32 4 32, .pow 2 3 37, .mul 32 37 32,
      .mul 32 1 32, .mul 32 4 32, .mul 32 6 32, .mul 32 5 32, .mul 32 2 32, .mul 32 5 32,
      .mul 32 6 32, .mul 32 4 32, .mul 32 6 32, .mul 32 0 32, .mul 32 12 38, .mul 38 25 39,
      .mul 12 39 40, .pow 1 0 41, .mul 41 3 41, .mul 41 0 41, .mul 41 4 41, .mul 41 2 41,
      .mul 41 4 41, .mul 41 3 41, .mul 41 2 41, .mul 41 3 41, .pow 2 5 42, .mul 41 42 41,
      .mul 41 3 41, .mul 41 0 41, .mul 41 2 41, .pow 2 6 43, .mul 41 43 41, .mul 41 0 41,
      .mul 41 4 41, .mul 41 3 41, .mul 41 2 41, .mul 41 6 41, .mul 41 5 41, .mul 41 6 41,
      .mul 41 5 41, .pow 2 6 44, .mul 41 44 41, .mul 41 5 41, .mul 41 6 41, .mul 41 4 41,
      .mul 41 1 41, .pow 3 4 45, .mul 41 45 41, .mul 41 3 41, .mul 41 1 41, .mul 41 0 41,
      .mul 41 5 41, .mul 41 6 41, .mul 41 4 41, .mul 41 1 41, .pow 1 2 46, .mul 46 5 46,
      .mul 46 3 46, .mul 46 4 46, .mul 46 0 46, .mul 46 2 46, .mul 46 6 46, .pow 3 5 47,
      .mul 46 47 46, .mul 46 2 46, .mul 46 5 46, .mul 46 3 46, .mul 46 4 46, .pow 2 3 48,
      .mul 46 48 46, .mul 46 4 46, .mul 46 3 46, .mul 46 4 46, .mul 46 3 46, .mul 46 1 46,
      .mul 46 6 46, .mul 46 5 46, .mul 46 0 46, .pow 2 3 49, .mul 46 49 46, .mul 46 1 46,
      .mul 46 0 46, .mul 46 6 46, .pow 2 4 50, .mul 46 50 46, .mul 46 6 46, .mul 46 1 46,
      .mul 46 6 46, .mul 46 5 46, .mul 46 1 46, .mul 46 5 46, .mul 46 0 46, .mul 46 6 46,
      .mul 46 0 46, .mul 46 12 51, .mul 51 41 52, .mul 12 52 53, .pow 17 53 54, .mul 41 54 55]
  rx := 24
  ry := 40
  rh := 55
  r := 7
  oh := 3
  a := 3
  b := 1
  c := 5
  d := 0
  t := 0

end CFSG.SectionRank.Native
