module

public import Certificates.Data.CFSGNative.HS.Cert

public section

namespace CFSG.Sporadic.HS.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

@[expose] def seedA : String := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m1"

@[expose] def seedB : String := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m2"

@[expose] def prog : List Instr := [
    .iv 0 3, .iv 1 4, .mu 1 4 5, .mu 5 3 5, .mu 5 1 5, .mu 5 0 5,
    .mu 5 0 5, .mu 5 3 5, .mu 5 4 5, .mu 5 3 5, .mu 5 1 5, .mu 5 4 5,
    .mu 5 1 5, .mu 5 4 5, .mu 5 4 5, .mu 5 1 5, .iv 5 6, .mu 1 6 7,
    .mu 7 3 7, .mu 7 4 7, .mu 7 4 7, .mu 7 3 7, .mu 7 4 7, .mu 7 3 7,
    .mu 7 1 7, .mu 7 0 7, .mu 7 1 7, .mu 7 3 7, .mu 7 1 7, .mu 7 0 7,
    .mu 7 3 7, .mu 7 1 7, .mu 7 1 7, .mu 7 0 7, .mu 7 0 7, .mu 7 4 7,
    .iv 7 8, .mu 6 7 9, .mu 9 6 9, .mu 9 8 9, .mu 9 8 9, .mu 9 6 9,
    .mu 9 7 9, .mu 9 7 9, .mu 9 3 9, .mu 9 1 9, .mu 9 1 9, .mu 9 8 9,
    .mu 9 1 9, .mu 9 4 9, .mu 9 0 9, .mu 9 1 9, .mu 9 0 9, .mu 9 4 9,
    .mu 9 3 9, .mu 9 0 9, .mu 9 1 9, .mu 9 4 9, .mu 9 4 9, .mu 9 0 9,
    .mu 9 0 9, .mu 9 0 9, .mu 9 4 9, .iv 9 10, .mu 6 7 11, .mu 11 7 11,
    .mu 11 6 11, .mu 11 8 11, .mu 11 4 11, .mu 11 4 11, .mu 11 6 11, .mu 11 1 11,
    .mu 11 1 11, .mu 11 1 11, .mu 11 3 11, .mu 11 0 11, .mu 11 1 11, .mu 11 0 11,
    .mu 11 0 11, .mu 11 0 11, .mu 11 0 11, .mu 11 3 11, .mu 11 4 11, .mu 11 1 11,
    .mu 11 1 11, .mu 11 3 11, .iv 11 12, .mu 8 9 13, .mu 13 7 13, .mu 13 7 13,
    .mu 13 10 13, .mu 13 4 13, .mu 13 8 13, .mu 13 8 13, .mu 13 6 13, .mu 13 1 13,
    .mu 13 1 13, .mu 13 1 13, .mu 13 1 13, .mu 13 4 13, .mu 13 0 13, .mu 13 0 13,
    .mu 13 3 13, .mu 13 1 13, .mu 13 3 13, .mu 13 1 13, .mu 13 3 13, .mu 13 1 13,
    .mu 13 3 13, .iv 13 14, .mu 7 6 15, .mu 15 8 15, .mu 15 12 15, .mu 15 4 15,
    .mu 15 3 15, .mu 15 10 15, .mu 15 1 15, .mu 15 4 15, .mu 15 1 15, .mu 15 4 15,
    .mu 15 4 15, .mu 15 0 15, .mu 15 4 15, .mu 15 3 15, .mu 15 3 15, .mu 15 0 15,
    .mu 15 4 15, .mu 15 4 15, .mu 15 3 15, .mu 15 0 15, .iv 15 16]

@[expose] def hsData (_ : Unit := ()) : VecData where
  d := 20
  seedA := seedA
  seedB := seedB
  expA := 2
  expB := 5
  v0 := 175
  n := 1100
  basis := #[
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 20, 21]
  basisInv := #[
      993284, 24160, 598215, 782189, 203586, 940509, 207412, 253970,
      941025, 102013, 575239, 260699, 1019067, 845383, 142946, 392419,
      577004, 163252, 354229, 163324]
  w0 := [
      1]
  w1 := [
      2]
  nregs := 17
  prog := prog
  sel := #[
      0, 1, 5, 7, 9, 11, 13, 15]
  base := #[
      0, 1, 2]
  qb := #[
      0, 1, 2]
  orbSizes := [
      1100, 280, 144]
  subReps := #[
      0, 1, 2, 8, 16]
  subSizes := [
      1, 280, 672, 105, 42]
  ord0 := (2, 1)
  ord1 := (5, 1)
  ord01 := (11, 1)

end CFSG.Sporadic.HS.Native
