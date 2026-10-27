module

public import Certificates.Data.CFSGNative.HS.Cert

public section

namespace CFSG.Sporadic.Ru.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

@[expose] def seedA : String := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m1"

@[expose] def seedB : String := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m2"

@[expose] def prog : List Instr := [
    .iv 0 3, .iv 1 4, .mu 1 3 5, .mu 5 1 5, .mu 5 0 5, .mu 5 0 5,
    .mu 5 3 5, .mu 5 4 5, .mu 5 3 5, .mu 5 3 5, .mu 5 0 5, .mu 5 1 5,
    .mu 5 3 5, .mu 5 1 5, .mu 5 3 5, .mu 5 1 5, .mu 5 1 5, .mu 5 4 5,
    .iv 5 6, .mu 4 6 7, .mu 7 4 7, .mu 7 4 7, .mu 7 5 7, .mu 7 4 7,
    .mu 7 3 7, .mu 7 3 7, .mu 7 4 7, .mu 7 3 7, .mu 7 0 7, .mu 7 4 7,
    .mu 7 4 7, .mu 7 3 7, .mu 7 3 7, .mu 7 3 7, .mu 7 4 7, .mu 7 4 7,
    .mu 7 1 7, .mu 7 4 7, .mu 7 3 7, .iv 7 8, .mu 6 8 9, .mu 9 8 9,
    .mu 9 5 9, .mu 9 5 9, .mu 9 4 9, .mu 9 6 9, .mu 9 4 9, .mu 9 5 9,
    .mu 9 3 9, .mu 9 0 9, .mu 9 0 9, .mu 9 1 9, .mu 9 1 9, .mu 9 0 9,
    .mu 9 3 9, .mu 9 1 9, .mu 9 3 9, .mu 9 4 9, .mu 9 1 9, .mu 9 4 9,
    .mu 9 3 9, .mu 9 4 9, .iv 9 10, .mu 7 10 11, .mu 11 5 11, .mu 11 9 11,
    .mu 11 6 11, .mu 11 3 11, .mu 11 6 11, .mu 11 1 11, .mu 11 5 11, .mu 11 3 11,
    .mu 11 3 11, .mu 11 1 11, .mu 11 1 11, .mu 11 3 11, .mu 11 1 11, .mu 11 4 11,
    .mu 11 3 11, .mu 11 1 11, .mu 11 1 11, .mu 11 0 11, .mu 11 1 11, .mu 11 0 11,
    .mu 11 0 11, .iv 11 12, .mu 12 12 13, .mu 13 9 13, .mu 13 11 13, .mu 13 9 13,
    .mu 13 8 13, .mu 13 12 13, .mu 13 8 13, .mu 13 9 13, .mu 13 5 13, .mu 13 3 13,
    .mu 13 8 13, .mu 13 8 13, .mu 13 4 13, .mu 13 10 13, .mu 13 0 13, .mu 13 3 13,
    .mu 13 4 13, .mu 13 3 13, .mu 13 4 13, .mu 13 0 13, .mu 13 4 13, .mu 13 4 13,
    .mu 13 4 13, .mu 13 1 13, .mu 13 3 13, .mu 13 3 13, .mu 13 1 13, .mu 13 3 13,
    .iv 13 14, .mu 14 14 15, .mu 15 10 15, .mu 15 12 15, .mu 15 9 15, .mu 15 14 15,
    .mu 15 12 15, .mu 15 5 15, .mu 15 8 15, .mu 15 12 15, .mu 15 5 15, .mu 15 8 15,
    .mu 15 3 15, .mu 15 6 15, .mu 15 4 15, .mu 15 4 15, .mu 15 5 15, .mu 15 3 15,
    .mu 15 1 15, .mu 15 0 15, .mu 15 4 15, .mu 15 3 15, .mu 15 3 15, .mu 15 1 15,
    .mu 15 4 15, .mu 15 0 15, .mu 15 1 15, .mu 15 1 15, .mu 15 1 15, .mu 15 1 15,
    .mu 15 3 15, .iv 15 16]

@[expose] def ruData (_ : Unit := ()) : VecData where
  d := 28
  seedA := seedA
  seedB := seedB
  expA := 2
  expB := 4
  v0 := 1
  n := 4060
  basis := #[
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
      17, 18, 19, 20, 22, 23, 25, 26, 27, 29, 30, 31]
  basisInv := #[
      1, 92790770, 242805528, 117876869, 104085288, 216591173, 221966218, 263652958,
      20266440, 38392212, 224802867, 115655616, 84730350, 4326366, 177032347, 120063968,
      26784423, 124344076, 211335290, 143353391, 136004693, 219625366, 10070683, 144835300,
      236343522, 170711562, 171486712, 64004669]
  w0 := [
      1]
  w1 := [
      -2, 1, 2, 2]
  nregs := 17
  prog := prog
  sel := #[
      0, 1, 5, 7, 9, 11, 13, 15]
  base := #[
      0, 1, 2, 3, 4]
  qb := #[
      0, 1, 2, 3, 4]
  orbSizes := [
      4060, 2304, 300, 13, 4]
  subReps := #[
      0, 1, 7]
  subSizes := [
      1, 2304, 1755]
  ord0 := (2, 1)
  ord1 := (13, 1)
  ord01 := (29, 1)

end CFSG.Sporadic.Ru.Native
