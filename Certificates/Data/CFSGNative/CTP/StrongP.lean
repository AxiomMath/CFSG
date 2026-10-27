module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def mclSylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 14
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 1 5,
      .mul 5 3 1, .mul 3 3 6, .mul 6 6 0, .mul 4 4 5,
      .mul 5 5 4, .pow 6 4 5, .mul 5 0 6, .mul 6 4 0,
      .mul 3 2 4, .mul 4 4 3, .mul 3 3 4, .pow 6 4 5,
      .mul 5 1 6, .mul 6 4 1, .pow 2 0 10, .pow 7 1 11,
      .pow 1 0 12, .mul 12 1 12, .mul 12 0 12, .mul 12 11 12,
      .pow 1 12 8, .pow 1 0 12, .mul 12 11 12, .mul 12 0 12,
      .mul 12 1 12, .pow 1 12 9]
  rx := 8
  ry := 9
  rh := 13
  r := 5
  oh := 1
  a := 1
  b := 0
  c := 0
  d := 1
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def lySylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/LyG1-f5r111B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/LyG1-f5r111B0.m2"
  nregs := 16
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5,
      .mul 5 2 6, .pow 13 2 4, .mul 4 0 8, .mul 8 2 0,
      .pow 3 6 1, .pow 12 3 5, .pow 4 5 4, .mul 4 1 2,
      .mul 2 5 1, .pow 1 0 12, .pow 2 1 13, .pow 1 0 14,
      .mul 14 1 14, .mul 14 0 14, .mul 14 13 14, .pow 5 14 10,
      .pow 1 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 1 14,
      .mul 14 0 14, .mul 14 13 14, .mul 14 0 14, .mul 14 13 14,
      .pow 2 14 11]
  rx := 10
  ry := 11
  rh := 15
  r := 5
  oh := 1
  a := 1
  b := 0
  c := 0
  d := 1
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def onSylow7Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
  nregs := 13
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 3 4, .pow 18 4 3,
      .mul 3 1 5, .mul 5 4 1, .pow 10 2 3, .mul 3 0 4,
      .mul 4 2 0, .pow 1 0 9, .pow 3 1 10, .pow 1 0 11,
      .mul 11 1 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11,
      .mul 11 1 11, .mul 11 1 11, .pow 4 11 7, .pow 1 0 11,
      .mul 11 1 11, .mul 11 1 11, .mul 11 0 11, .mul 11 10 11,
      .mul 11 0 11, .mul 11 10 11, .pow 4 11 8]
  rx := 7
  ry := 8
  rh := 12
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

@[expose] def co3Sylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
  nregs := 16
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .pow 3 2 6,
      .pow 9 4 7, .mul 6 7 5, .pow 29 5 8, .mul 8 1 6,
      .mul 6 5 1, .pow 2 0 12, .pow 3 1 13, .pow 1 0 14,
      .mul 14 1 14, .mul 14 12 14, .mul 14 1 14, .mul 14 1 14,
      .pow 2 14 10, .pow 1 1 14, .mul 14 1 14, .mul 14 12 14,
      .mul 14 1 14, .mul 14 0 14, .pow 2 14 11]
  rx := 10
  ry := 11
  rh := 15
  r := 5
  oh := 1
  a := 1
  b := 0
  c := 0
  d := 1
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def co2Sylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
  nregs := 13
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 1 4, .mul 4 1 5,
      .pow 3 3 0, .mul 4 4 3, .mul 2 2 4, .mul 4 3 1,
      .pow 5 1 3, .pow 20 5 4, .pow 6 2 5, .mul 4 5 2,
      .pow 7 2 4, .mul 4 3 5, .mul 5 2 1, .pow 2 0 9,
      .pow 3 1 10, .pow 1 0 11, .mul 11 10 11, .pow 4 11 7,
      .pow 1 9 11, .mul 11 1 11, .pow 4 11 8]
  rx := 7
  ry := 8
  rh := 12
  r := 5
  oh := 1
  a := 1
  b := 0
  c := 0
  d := 1
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def hnSylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HNG1-f5r133B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HNG1-f5r133B0.m2"
  nregs := 15
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5,
      .mul 5 2 6, .mul 6 3 7, .mul 0 5 2, .mul 2 7 3,
      .pow 19 3 2, .pow 29 2 3, .mul 3 1 4, .mul 4 2 1,
      .pow 10 5 0, .pow 1 0 11, .pow 2 1 12, .pow 1 0 13,
      .mul 13 1 13, .pow 4 13 9, .pow 1 0 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 1 13, .mul 13 0 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 12 13, .pow 4 13 10]
  rx := 9
  ry := 10
  rh := 14
  r := 5
  oh := 1
  a := 1
  b := 0
  c := 0
  d := 1
  k := 0
  l := 0
  μ := 1
  t := 0

@[expose] def thSylow5Data : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  nregs := 14
  prog := [
      .mul 0 1 2, .mul 2 1 3, .pow 5 2 4, .mul 4 1 5,
      .pow 5 5 1, .pow 3 2 4, .pow 15 3 5, .mul 4 5 6,
      .pow 17 6 5, .mul 5 0 4, .mul 4 6 0, .pow 8 3 4,
      .pow 9 2 5, .mul 4 5 6, .pow 19 6 5, .mul 5 1 4,
      .mul 4 6 1, .pow 1 0 10, .pow 3 1 11, .pow 1 0 12,
      .mul 12 11 12, .mul 12 0 12, .mul 12 1 12, .pow 2 12 8,
      .pow 1 0 12, .mul 12 1 12, .mul 12 0 12, .mul 12 1 12,
      .mul 12 1 12, .mul 12 0 12, .mul 12 11 12, .pow 1 12 9]
  rx := 8
  ry := 9
  rh := 13
  r := 5
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
