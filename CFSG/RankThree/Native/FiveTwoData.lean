module

public import CFSG.RankThree.Native.FiveTwoCert

public section

namespace CFSG.RankThree.Native

open CFSG.SectionRank.Native

@[expose] def j3FiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/J3G1-f2r80B0.m1"
      seedB := include_str "../../Blueprint/Data/J3G1-f2r80B0.m2"
      nregs := 18
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 1 8,
        .mul 8 1 9, .mul 9 0 10, .mul 10 1 11, .mul 11 0 12, .mul 12 1 13, .mul 13 1 14,
        .mul 14 0 15, .mul 15 1 16, .mul 16 1 17]
      outs := []
      tests := [0] }
  w := 17

@[expose] def co1FiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/Co1G1-f2r24B0.m1"
      seedB := include_str "../../Blueprint/Data/Co1G1-f2r24B0.m2"
      nregs := 4
      prog := [.mul 0 1 2, .pow 4 2 3]
      outs := []
      tests := [0] }
  w := 3

@[expose] def co2FiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/Co2G1-f2r22B0.m1"
      seedB := include_str "../../Blueprint/Data/Co2G1-f2r22B0.m2"
      nregs := 9
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 1 7, .pow 3 7 8]
      outs := []
      tests := [0] }
  w := 8

@[expose] def co3FiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/Co3G1-f2r22B0.m1"
      seedB := include_str "../../Blueprint/Data/Co3G1-f2r22B0.m2"
      nregs := 5
      prog := [.mul 0 1 2, .mul 2 1 3, .mul 3 1 4]
      outs := []
      tests := [0] }
  w := 4

@[expose] def hsFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/HSG1-f2r20B0.m1"
      seedB := include_str "../../Blueprint/Data/HSG1-f2r20B0.m2"
      nregs := 4
      prog := [.mul 0 1 2, .mul 2 1 3]
      outs := []
      tests := [0] }
  w := 3

@[expose] def mclFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/McLG1-f3r21B0.m1"
      seedB := include_str "../../Blueprint/Data/McLG1-f3r21B0.m2"
      nregs := 11
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 1 7, .mul 7 1 8,
        .mul 8 1 9, .pow 3 9 10]
      outs := []
      tests := [0] }
  w := 10

@[expose] def hnFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/HNG1-f5r133B0.m1"
      seedB := include_str "../../Blueprint/Data/HNG1-f5r133B0.m2"
      nregs := 9
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 1 7, .pow 2 7 8]
      outs := []
      tests := [0] }
  w := 8

@[expose] def suzFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/SuzG1-f3r64B0.m1"
      seedB := include_str "../../Blueprint/Data/SuzG1-f3r64B0.m2"
      nregs := 16
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 1 8,
        .mul 8 0 9, .mul 9 1 10, .mul 10 1 11, .mul 11 0 12, .mul 12 1 13, .mul 13 1 14,
        .pow 2 14 15]
      outs := []
      tests := [0] }
  w := 15

@[expose] def lyFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/LyG1-f5r111B0.m1"
      seedB := include_str "../../Blueprint/Data/LyG1-f5r111B0.m2"
      nregs := 5
      prog := [.mul 0 1 2, .mul 2 1 3, .pow 3 3 4]
      outs := []
      tests := [0] }
  w := 4

@[expose] def thFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/ThG1-f2r248B0.m1"
      seedB := include_str "../../Blueprint/Data/ThG1-f2r248B0.m2"
      nregs := 6
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 1 5]
      outs := []
      tests := [0] }
  w := 5

@[expose] def onFiveTwo : FiveTwoData where
  base :=
    { seedA := include_str "../../Blueprint/Data/ONG1-f3r154B0.m1"
      seedB := include_str "../../Blueprint/Data/ONG1-f3r154B0.m2"
      nregs := 7
      prog := [.mul 0 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 1 5, .pow 2 5 6]
      outs := []
      tests := [0] }
  w := 6

end CFSG.RankThree.Native
