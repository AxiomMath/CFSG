module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def fi22MultFive (_ : Unit := ()) : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F22G1-f3r77B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F22G1-f3r77B0.m2"
  nregs := 8
  prog := [.mul 0 1 2, .pow 4 2 2, .mul 2 0 2, .mul 0 1 3, .pow 7 3 3, .mul 2 3 2,
      .mul 0 1 3, .mul 3 1 3, .pow 16 3 3, .mul 1 0 4, .mul 4 1 4, .mul 4 1 4,
      .mul 3 4 3, .mul 0 1 4, .mul 4 1 4, .pow 5 4 4, .mul 3 4 3, .pow 8 3 4,
      .mul 3 3 5, .mul 5 2 5, .pow 2 5 5, .mul 2 3 6, .mul 4 2 7, .mul 6 2 6,
      .mul 6 3 6, .mul 6 3 6, .mul 6 3 6, .mul 2 7 7, .mul 4 7 7, .mul 2 7 7,
      .mul 4 7 7, .mul 4 7 7, .mul 4 7 7, .mul 4 7 7, .mul 6 3 6, .mul 6 3 6,
      .mul 6 3 6, .mul 6 3 6, .mul 2 7 7, .mul 4 7 7, .mul 2 7 7, .mul 6 3 6,
      .mul 6 2 6, .mul 6 3 6, .mul 6 3 6, .mul 6 7 6, .mul 4 2 7, .mul 4 7 7,
      .mul 2 7 7, .mul 4 7 7, .mul 2 7 7, .mul 4 7 7, .mul 4 7 7, .mul 4 7 7,
      .mul 2 7 7, .mul 4 7 4, .mul 3 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 3 7,
      .mul 7 3 7, .mul 7 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7,
      .mul 2 4 4, .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7, .mul 7 4 7]
  rx := 5
  ry := 6
  rh := 7
  r := 5
  oh := 20
  a := 4
  b := 2
  c := 2
  d := 4
  t := 0

@[expose] def fi23MultFive (_ : Unit := ()) : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F23G1-f3r253B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F23G1-f3r253B0.m2"
  nregs := 12
  prog := [.mul 0 1 2, .pow 9 2 2, .mul 0 1 3, .mul 3 1 3, .pow 12 3 3, .mul 2 3 2,
      .mul 0 1 3, .pow 9 3 3, .mul 2 3 2, .pow 17 2 3, .mul 0 0 4, .mul 4 2 4,
      .pow 9 4 4, .mul 0 4 4, .mul 4 0 4, .mul 3 4 5, .mul 5 2 5, .mul 2 4 4,
      .mul 4 3 4, .mul 0 5 6, .mul 6 0 6, .mul 0 4 7, .mul 7 0 7, .mul 2 6 8,
      .mul 8 3 8, .mul 3 7 9, .mul 9 2 9, .mul 0 8 10, .mul 10 0 10, .mul 0 9 11,
      .mul 11 0 11, .mul 3 9 3, .mul 3 2 3, .mul 0 3 3, .mul 3 0 3, .mul 4 3 4,
      .mul 4 5 4, .mul 4 11 4, .mul 7 8 7, .mul 7 9 7, .mul 7 6 7, .mul 10 5 10]
  rx := 4
  ry := 7
  rh := 10
  r := 5
  oh := 2
  a := 4
  b := 0
  c := 0
  d := 1
  t := 0

@[expose] def fi24MultFive (_ : Unit := ()) : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m2"
  nregs := 7
  prog := [.pow 2 1 2, .mul 0 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
      .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 2 3, .mul 3 0 3, .mul 3 2 3,
      .mul 3 0 3, .mul 3 2 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
      .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .pow 3 3 3, .mul 1 0 4,
      .mul 4 1 4, .mul 4 0 4, .mul 4 2 5, .mul 5 0 5, .mul 5 2 5, .mul 5 0 5,
      .mul 5 2 5, .mul 4 1 4, .mul 4 0 4, .mul 4 2 4, .mul 4 0 4, .mul 4 2 4,
      .mul 5 0 5, .mul 5 4 5, .pow 4 3 4, .mul 5 3 2, .mul 2 5 2, .mul 2 3 2,
      .mul 2 5 2, .mul 2 3 2, .mul 2 5 2, .mul 2 4 2, .pow 3 2 2, .mul 5 2 4,
      .mul 4 2 3, .mul 4 3 6, .mul 3 2 3, .mul 3 2 3, .mul 6 3 6, .mul 6 4 6,
      .mul 6 6 4, .mul 4 5 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4, .mul 4 6 4,
      .pow 4 4 4, .mul 5 6 3, .mul 3 6 3, .mul 3 6 3, .mul 3 6 3, .mul 3 6 3,
      .mul 3 6 3, .pow 8 3 3]
  rx := 4
  ry := 3
  rh := 5
  r := 5
  oh := 2
  a := 1
  b := 0
  c := 1
  d := 4
  t := 0

@[expose] def fi24MultSeven (_ : Unit := ()) : CubData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m2"
  nregs := 7
  prog := [.pow 2 1 2, .mul 0 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
      .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 2 3, .mul 3 0 3, .mul 3 2 3,
      .mul 3 0 3, .mul 3 2 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
      .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .pow 3 3 3, .mul 1 0 4,
      .mul 4 1 4, .mul 4 0 4, .mul 4 2 5, .mul 5 0 5, .mul 5 2 5, .mul 5 0 5,
      .mul 5 2 5, .mul 4 1 4, .mul 4 0 4, .mul 4 2 4, .mul 4 0 4, .mul 4 2 4,
      .mul 5 0 5, .mul 5 4 5, .pow 4 3 4, .mul 5 3 2, .mul 2 5 2, .mul 2 3 2,
      .mul 2 5 2, .mul 2 3 2, .mul 2 5 2, .mul 2 4 2, .pow 3 2 2, .mul 5 2 5,
      .mul 5 2 2, .mul 5 2 4, .mul 2 2 2, .mul 2 2 3, .mul 2 3 3, .pow 7 5 5,
      .pow 16 5 6, .mul 6 3 6, .mul 6 5 6, .pow 5 4 4, .pow 2 4 5, .mul 5 2 5,
      .mul 5 4 5, .mul 6 5 4, .pow 3 4 2, .mul 5 6 5, .pow 3 5 5]
  rx := 2
  ry := 5
  rh := 4
  r := 7
  oh := 21
  a := 1
  b := 0
  c := 0
  d := 4
  k := 0
  l := 6
  μ := 4
  t := 0
