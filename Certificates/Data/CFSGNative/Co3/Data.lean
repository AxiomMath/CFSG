module

public import Certificates.Data.CFSGNative.HS.Cert

public section

namespace CFSG.Sporadic.Co3.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

@[expose] def seedA : String := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"

@[expose] def seedB : String := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"

@[expose] def prog : List Instr := [
    .iv 0 3, .iv 1 4, .mu 4 0 5, .mu 5 1 5, .mu 5 3 5, .mu 5 4 5,
    .mu 5 0 5, .mu 5 4 5, .mu 5 0 5, .mu 5 4 5, .mu 5 3 5, .mu 5 1 5,
    .mu 5 4 5, .mu 5 3 5, .mu 5 3 5, .mu 5 1 5, .mu 5 0 5, .mu 5 1 5,
    .mu 5 1 5, .mu 5 0 5, .mu 5 1 5, .mu 5 0 5, .mu 5 1 5, .mu 5 1 5,
    .mu 5 1 5, .mu 5 4 5, .iv 5 6, .mu 3 5 7, .mu 7 5 7, .mu 7 5 7,
    .mu 7 5 7, .mu 7 1 7, .mu 7 1 7, .mu 7 0 7, .mu 7 4 7, .mu 7 0 7,
    .mu 7 3 7, .mu 7 1 7, .mu 7 1 7, .mu 7 3 7, .mu 7 1 7, .mu 7 1 7,
    .mu 7 0 7, .mu 7 1 7, .mu 7 1 7, .mu 7 1 7, .iv 7 8, .mu 6 8 9,
    .mu 9 6 9, .mu 9 6 9, .mu 9 6 9, .mu 9 6 9, .mu 9 6 9, .mu 9 0 9,
    .mu 9 7 9, .mu 9 7 9, .mu 9 6 9, .mu 9 4 9, .mu 9 3 9, .mu 9 0 9,
    .mu 9 4 9, .mu 9 3 9, .mu 9 4 9, .mu 9 1 9, .mu 9 3 9, .mu 9 0 9,
    .mu 9 4 9, .mu 9 1 9, .mu 9 1 9, .mu 9 0 9, .mu 9 1 9, .iv 9 10,
    .mu 5 7 11, .mu 11 9 11, .mu 11 7 11, .mu 11 7 11, .mu 11 0 11, .mu 11 6 11,
    .mu 11 6 11, .mu 11 4 11, .mu 11 5 11, .mu 11 3 11, .mu 11 1 11, .mu 11 4 11,
    .mu 11 1 11, .mu 11 0 11, .mu 11 4 11, .mu 11 3 11, .mu 11 4 11, .mu 11 1 11,
    .mu 11 1 11, .mu 11 0 11, .mu 11 3 11, .mu 11 3 11, .mu 11 4 11, .iv 11 12,
    .mu 10 10 13, .mu 13 10 13, .mu 13 10 13, .mu 13 12 13, .mu 13 9 13, .mu 13 7 13,
    .mu 13 6 13, .mu 13 10 13, .mu 13 8 13, .mu 13 9 13, .mu 13 5 13, .mu 13 0 13,
    .mu 13 12 13, .mu 13 3 13, .mu 13 5 13, .mu 13 7 13, .mu 13 3 13, .mu 13 3 13,
    .mu 13 3 13, .mu 13 0 13, .mu 13 4 13, .mu 13 3 13, .mu 13 3 13, .mu 13 0 13,
    .mu 13 3 13, .mu 13 0 13, .mu 13 1 13, .mu 13 3 13, .mu 13 4 13, .mu 13 3 13,
    .iv 13 14, .mu 10 12 15, .mu 15 10 15, .mu 15 14 15, .mu 15 9 15, .mu 15 12 15,
    .mu 15 8 15, .mu 15 8 15, .mu 15 8 15, .mu 15 12 15, .mu 15 7 15, .mu 15 0 15,
    .mu 15 5 15, .mu 15 4 15, .mu 15 9 15, .mu 15 4 15, .mu 15 0 15, .mu 15 4 15,
    .mu 15 4 15, .mu 15 1 15, .mu 15 4 15, .mu 15 0 15, .mu 15 3 15, .mu 15 3 15,
    .mu 15 1 15, .mu 15 0 15, .mu 15 1 15, .mu 15 4 15, .mu 15 1 15, .mu 15 4 15,
    .iv 15 16, .mu 16 14 17, .mu 17 15 17, .mu 17 9 17, .mu 17 9 17, .mu 17 12 17,
    .mu 17 15 17, .mu 17 6 17, .mu 17 7 17, .mu 17 7 17, .mu 17 9 17, .mu 17 5 17,
    .mu 17 3 17, .mu 17 7 17, .mu 17 14 17, .mu 17 1 17, .mu 17 3 17, .mu 17 3 17,
    .mu 17 4 17, .mu 17 4 17, .mu 17 3 17, .mu 17 3 17, .mu 17 0 17, .mu 17 1 17,
    .mu 17 0 17, .mu 17 4 17, .mu 17 0 17, .mu 17 1 17, .mu 17 3 17, .mu 17 1 17,
    .iv 17 18]

@[expose] def co3Data (_ : Unit := ()) : VecData where
  d := 22
  seedA := seedA
  seedB := seedB
  expA := 3
  expB := 4
  v0 := 1
  n := 11178
  basis := #[
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 20, 22, 25]
  basisInv := #[
      1, 7505, 2155403, 2150670, 79854, 1597336, 2309598, 857191,
      3718894, 1951343, 2719169, 2266754, 3597857, 25567, 1225751, 167917,
      3146643, 2363158, 737073, 2029719, 3145636, 1600478]
  w0 := [
      1]
  w1 := [
      -2, -2, -1, -2, -1, 2, 1, 2, 1, 2, 2]
  nregs := 19
  prog := prog
  sel := #[
      0, 1, 5, 7, 9, 11, 13, 15, 17]
  base := #[
      0, 1, 2, 3, 4]
  qb := #[
      0, 1, 2, 3, 4]
  orbSizes := [
      11178, 5600, 165, 24, 2]
  subReps := #[
      0, 1, 2, 5, 6]
  subSizes := [
      1, 5600, 352, 4125, 1100]
  ord0 := (3, 1)
  ord1 := (2, 2)
  ord01 := (23, 1)

end CFSG.Sporadic.Co3.Native
